//===--- ImplementVirtualMethods.cpp --------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "ParsedAST.h"
#include "refactor/InsertionPoint.h"
#include "refactor/Tweak.h"
#include "clang/AST/Attr.h"
#include "clang/AST/CXXInheritance.h"
#include "clang/AST/PrettyPrinter.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/ADT/iterator_range.h"
#include "llvm/Support/Error.h"

namespace clang {
namespace clangd {
namespace {

// This tweak offers to add implementations of all pure-virtual methods.
// If there are none, it offers to add implementations of virtual methods.
class ImplementVirtualMethods : public Tweak {
public:
  const char *id() const override final;
  llvm::StringLiteral kind() const override {
    return CodeAction::REFACTOR_KIND;
  }
  std::string title() const override {
    const char *Verb = PureMethods.empty() ? "Override" : "Implement";
    const char *Adjective = PureMethods.empty() ? "virtual" : "missing";
    const std::vector<const CXXMethodDecl *> &Methods =
        PureMethods.empty() ? VirtualMethods : PureMethods;
    if (Methods.size() == 1)
      return llvm::formatv("{0} {1} method {2}", Verb, Adjective,
                           Methods.front()->getDeclName());
    return llvm::formatv("{0} {1} {2} methods", Verb, Methods.size(),
                         Adjective);
  }

  bool prepare(const Selection &Inputs) override {
    const auto *N = Inputs.ASTSelection.commonAncestor();
    if (!N)
      return false;
    // Trigger on a class definition, and detect the base to implement.
    if (const auto *CRD = N->ASTNode.get<CXXRecordDecl>()) {
      if (CRD->isThisDeclarationADefinition())
        return chooseTarget(*CRD);
    }
    // Trigger anywhere inside a base specifier.
    for (; N; N = N->Parent)
      if (const CXXBaseSpecifier *CBS = N->ASTNode.get<CXXBaseSpecifier>()) {
        // Need to find enclosing class.
        for (; N; N = N->Parent)
          if (const CXXRecordDecl *CRD = N->ASTNode.get<CXXRecordDecl>())
            return chooseTarget(*CRD);
        break;
      }
    return false;
  }

  Expected<Tweak::Effect> apply(const Selection &Inputs) override {
    const std::vector<const CXXMethodDecl *> &Methods =
        PureMethods.empty() ? VirtualMethods : PureMethods;

    struct HandleScope : public PrintingCallbacks {
      const CXXRecordDecl *Class;
      mutable CXXBasePaths Paths;
      HandleScope(const CXXRecordDecl *Class) : Class(Class), Paths() {}
      virtual ~HandleScope() = default;

      bool isScopeVisible(const clang::DeclContext *DC) const override {
        if (DC->Encloses(Class))
          return true;
        if (const auto *MaybeBase = llvm::dyn_cast<CXXRecordDecl>(DC))
          if (Class->isDerivedFrom(MaybeBase, Paths))
            return true;
        return false;
      }
    } PCallbacks(Class);
    PrintingPolicy PP(Inputs.AST->getASTContext().getPrintingPolicy());
    PP.PolishForDeclaration = true;
    PP.TerseOutput = true;
    PP.Callbacks = &PCallbacks;
    std::string Code;
    llvm::raw_string_ostream OS(Code);
    for (const CXXMethodDecl *Method : Methods)
      reprint(*Method, OS, PP);
    // FIXME: access control

    // Prefer to place the new members...
    std::vector<Anchor> Anchors = {
        // Below the default constructor
        {[](const Decl *D) {
           if (const auto *CCD = llvm::dyn_cast<CXXConstructorDecl>(D))
             return CCD->isDefaultConstructor();
           return false;
         },
         Anchor::Below},
        // Above existing constructors
        {[](const Decl *D) { return llvm::isa<CXXConstructorDecl>(D); },
         Anchor::Above},
        // At the top of the public section
        {[](const Decl *D) { return true; }, Anchor::Above},
    };
    auto Edit = insertDecl(Code, *Class, std::move(Anchors), AS_public);
    if (!Edit)
      return Edit.takeError();
    return Effect::mainFileEdit(Inputs.AST->getSourceManager(),
                                tooling::Replacements{std::move(*Edit)});
  }

private:
  // If (Class, BaseSpec) are a suitable target for this tweak,
  // populates this->{Class, MissingMethods, VirtualMethods} and returns true.
  bool chooseTarget(const CXXRecordDecl &Class) {
    if (!Class.isThisDeclarationADefinition() || Class.bases().empty())
      return false;

    auto HasDisqualifyingOverride = [&Class](const OverridingMethods &O) {
      for (const auto &OverridersInSubobject : O) {
        for (const auto &Overrider : OverridersInSubobject.second) {
          if (Overrider.InVirtualSubobject == &Class ||
              Overrider.Method->hasAttr<FinalAttr>())
            return true;
        }
      }
      return false;
    };

    CXXFinalOverriderMap FinalOverriders;
    Class.getFinalOverriders(FinalOverriders);
    for (const auto &Entry : FinalOverriders) {
      if (Entry.first->getDeclContext() == &Class)
        continue;
      if (Entry.first->size_overridden_methods() != 0)
        continue;
      if (Entry.first->isPure() && Entry.second.size() == 0)
        PureMethods.push_back(Entry.first);
      if (Entry.first->isVirtual() && !HasDisqualifyingOverride(Entry.second))
        VirtualMethods.push_back(Entry.first);
    }
    this->Class = &Class;
    return !PureMethods.empty() || !VirtualMethods.empty();
  }

  void reprint(const CXXMethodDecl &M, llvm::raw_string_ostream &OS,
               const PrintingPolicy &PP) {
    std::string Declarator;
    {
      llvm::raw_string_ostream OS(Declarator);
      const char *Sep = "";
      OS << M.getDeclName() << "(";
      for (const auto &Param : M.parameters()) {
        OS << Sep;
        Param->print(OS, PP);
        Sep = ", ";
      }
      OS << ")";
    }
    M.getReturnType().print(OS, PP, Declarator);
    M.getMethodQualifiers().print(OS, PP, /*appendSpaceIfNonEmpty=*/true);
    switch (M.getRefQualifier()) {
    case RQ_None:
      break;
    case RQ_LValue:
      OS << " &";
      break;
    case RQ_RValue:
      OS << " &&";
      break;
    }
    OS << " override {}\n";
  }

  // class Class : public Base.
  const CXXRecordDecl *Class;
  std::vector<const CXXMethodDecl *> PureMethods;
  std::vector<const CXXMethodDecl *> VirtualMethods;
};

REGISTER_TWEAK(ImplementVirtualMethods)

} // namespace
} // namespace clangd
} // namespace clang
