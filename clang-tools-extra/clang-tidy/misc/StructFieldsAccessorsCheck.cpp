//===--- StructFieldsAccessorsCheck.cpp - clang-tidy ----------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "StructFieldsAccessorsCheck.h"
#include "clang/AST/ASTContext.h"
#include "clang/Tooling/FixIt.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"

using namespace clang::ast_matchers;
using namespace clang::tooling::fixit;

namespace clang {
namespace tidy {
namespace misc {

void StructFieldsAccessorsCheck::registerMatchers(MatchFinder *Finder) {
  // let stype recordDecl(matchesName("foo$"))
  // m declRefExpr(hasParent(memberExpr().bind("mexp")),hasType(stype))
  // m declRefExpr(hasParent(memberExpr(hasParent(binaryOperator().bind("bop")))),hasType(stype))
  // m binaryOperator(isAssignmentOperator(),hasLHS(memberExpr(hasDescendant(declRefExpr())))).bind("addSetter")
  // m binaryOperator(isAssignmentOperator(),hasLHS(hasDescendant(declRefExpr(hasType(stype)))))
  // m binaryOperator(hasLHS(hasDescendant(declRefExpr(hasType(stype)))))
  // let lhs  binaryOperator(isAssignmentOperator(),hasLHS(hasDescendant(declRefExpr(hasType(stype)))))
  // m declRefExpr(hasType(stype),unless(hasAncestor(lhs)))
  // m declRefExpr(hasType(stype),unless(hasAncestor(lhs)),hasParent(memberExpr().bind("addGetter")))
  
  // And the winners are:
  // let stype recordDecl(matchesName("foo$"))     // TODO should really be matchesName("^foo$") to exclude struct oofoo and struct bar foo, but matching begining of string doesn't seem to work
  // let lhs binaryOperator(isAssignmentOperator(),hasLHS(hasDescendant(declRefExpr(hasType(stype)))))
  // m binaryOperator(isAssignmentOperator(),hasLHS(memberExpr(hasDescendant(declRefExpr())))).bind("addSetter")
  // m declRefExpr(hasType(stype),unless(hasAncestor(lhs)),hasParent(memberExpr().bind("addGetter")))

  // const auto attrMatcher = hasAttr(clang::attr::Annotate);
  const auto insecureStruct = recordDecl(
    // matchesName("__polymorphic$")
    hasAttr(clang::attr::Annotate)
  );

  Finder->addMatcher(
    insecureStruct.bind("addAccessors")
    , this);

  Finder->addMatcher(
    binaryOperator(
      isAssignmentOperator(),
      hasLHS(
        memberExpr(
          hasDescendant(
            declRefExpr()
          )
        )
      )
    ).bind("addSetter"),
    this
  );

  const auto lhs = 
    binaryOperator(
      isAssignmentOperator(),
      hasLHS(hasDescendant(
        declRefExpr(hasType(insecureStruct)))));

  Finder->addMatcher(
    declRefExpr(
      hasType(insecureStruct),
      unless(hasAncestor(lhs)),
      hasParent(memberExpr().bind("addGetter"))
    ),
    this
  );
}

void StructFieldsAccessorsCheck::check(const MatchFinder::MatchResult &Result) {
  const auto context = Result.Context;
  if (const auto MatchedDecl = Result.Nodes.getNodeAs<RecordDecl>("addAccessors"))
  {
    checkStruct(MatchedDecl);
  }
  if (const auto MatchedStmt = Result.Nodes.getNodeAs<BinaryOperator>("addSetter"))
  {
    checkSetters(MatchedStmt, context);
  }
  if (const auto MatchedExpr = Result.Nodes.getNodeAs<MemberExpr>("addGetter"))
  {
    checkGetters(MatchedExpr);
  }  
}

void StructFieldsAccessorsCheck::checkStruct(const clang::RecordDecl *const MatchedDecl) {
    const llvm::StringRef code_template = R"_HERESTR0_(}; 

#define PV_SECURED

int a_mask = 0;
int b_mask = 0;
 
void a_set(struct foo *p, int new_a){
  a_mask = rand();
  p->a = new_a ^ a_mask;
} 

int a_get(struct foo *p){
  int temp = p->a ^ a_mask;
  a_set(p, temp);
  return temp;
}

void b_set(struct foo *p, int new_b){
  b_mask = rand();
  p->b = new_b ^ b_mask;
}

int b_get(struct foo *p){
  int temp = p->b ^ b_mask;
  b_set(p, temp);
  return temp;
}

struct dummy {int dummy;)_HERESTR0_";

    diag(MatchedDecl->getLocation(), "struct is insecure") 
      << FixItHint::CreateInsertion(MatchedDecl->getEndLoc(), code_template); 
}

void StructFieldsAccessorsCheck::checkSetters(const clang::BinaryOperator *const MatchedStmt, ASTContext *const context) {
    if(const auto lhsMemberExpr = llvm::dyn_cast<MemberExpr>(MatchedStmt->getLHS())) {
      if(auto const valueDecl = llvm::dyn_cast<ValueDecl>(lhsMemberExpr->getMemberDecl())) {
        const auto memberDeclName = valueDecl->getNameAsString();

        if(const auto declRefExpr = llvm::dyn_cast<DeclRefExpr>(lhsMemberExpr->getBase())) {

          const auto declarationNameInfo = declRefExpr->getNameInfo();
          const auto name = declarationNameInfo.getAsString();

          if(const auto rhsExpr = llvm::dyn_cast<const Expr>(MatchedStmt->getRHS())) {

            const auto rhsText = (std::__1::string)getText(*rhsExpr, *context);

            const auto replacementRange = SourceRange(MatchedStmt->getBeginLoc(), MatchedStmt->getEndLoc());
            diag(MatchedStmt->getBeginLoc(), "struct field assignment is insecure")
              << FixItHint::CreateReplacement(replacementRange, memberDeclName + "_set(&" + name + ", " + rhsText + ")");

          } else {
            diag(MatchedStmt->getBeginLoc(),"FAIL!!! No RHS (Expr) !!");
          }
        } else {
          diag(MatchedStmt->getBeginLoc(),"FAIL!!! No Base (DeclRefExpr) !!");
        }
      } else {
          diag(MatchedStmt->getBeginLoc(),"FAIL!!! No MemberDecl !!");
      }
    } else {
      diag(MatchedStmt->getBeginLoc(),"FAIL!!! No MemberExpr !!");
    }
}

void StructFieldsAccessorsCheck::checkGetters(const clang::MemberExpr *const MatchedExpr) {
    const auto replacementRange = SourceRange(MatchedExpr->getBeginLoc(), MatchedExpr->getEndLoc());

    if(auto const valueDecl = llvm::dyn_cast<ValueDecl>(MatchedExpr->getMemberDecl())) {
      const auto memberDeclName = valueDecl->getNameAsString();

        if(const auto declRefExpr = llvm::dyn_cast<DeclRefExpr>(MatchedExpr->getBase())) {

          const auto declarationNameInfo = declRefExpr->getNameInfo();
          const auto name = declarationNameInfo.getAsString();

          diag(MatchedExpr->getBeginLoc(), "struct field access is insecure")
            << FixItHint::CreateReplacement(replacementRange, memberDeclName + "_get(&" + name + ")");

        }
    }
}

} // namespace misc
} // namespace tidy
} // namespace clang
