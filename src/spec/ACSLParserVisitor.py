# Generated from ACSLParser.g4 by ANTLR 4.13.2
from antlr4 import *

if "." in __name__:
    from .ACSLParser import ACSLParser
else:
    from ACSLParser import ACSLParser

# This class defines a complete generic visitor for a parse tree produced by ACSLParser.


class ACSLParserVisitor(ParseTreeVisitor):

    # Visit a parse tree produced by ACSLParser#logicParaVar.
    def visitLogicParaVar(self, ctx: ACSLParser.LogicParaVarContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#logicAtomicType.
    def visitLogicAtomicType(self, ctx: ACSLParser.LogicAtomicTypeContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#logicConstant.
    def visitLogicConstant(self, ctx: ACSLParser.LogicConstantContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#term.
    def visitTerm(self, ctx: ACSLParser.TermContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#pred.
    def visitPred(self, ctx: ACSLParser.PredContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#binder.
    def visitBinder(self, ctx: ACSLParser.BinderContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#funcContract.
    def visitFuncContract(self, ctx: ACSLParser.FuncContractContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#simpleClause.
    def visitSimpleClause(self, ctx: ACSLParser.SimpleClauseContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#terminatesClause.
    def visitTerminatesClause(self, ctx: ACSLParser.TerminatesClauseContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#assignsClause.
    def visitAssignsClause(self, ctx: ACSLParser.AssignsClauseContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#locations.
    def visitLocations(self, ctx: ACSLParser.LocationsContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#locationsList.
    def visitLocationsList(self, ctx: ACSLParser.LocationsListContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#location.
    def visitLocation(self, ctx: ACSLParser.LocationContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#requiresClause.
    def visitRequiresClause(self, ctx: ACSLParser.RequiresClauseContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#decreasesClause.
    def visitDecreasesClause(self, ctx: ACSLParser.DecreasesClauseContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#ensuresClause.
    def visitEnsuresClause(self, ctx: ACSLParser.EnsuresClauseContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#namedBehavior.
    def visitNamedBehavior(self, ctx: ACSLParser.NamedBehaviorContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#behaviorBody.
    def visitBehaviorBody(self, ctx: ACSLParser.BehaviorBodyContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#assumesClause.
    def visitAssumesClause(self, ctx: ACSLParser.AssumesClauseContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#completenessClause.
    def visitCompletenessClause(self, ctx: ACSLParser.CompletenessClauseContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#tset.
    def visitTset(self, ctx: ACSLParser.TsetContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#range.
    def visitRange(self, ctx: ACSLParser.RangeContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#assertion.
    def visitAssertion(self, ctx: ACSLParser.AssertionContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#cStatement.
    def visitCStatement(self, ctx: ACSLParser.CStatementContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#loopAnnot.
    def visitLoopAnnot(self, ctx: ACSLParser.LoopAnnotContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#loopClause.
    def visitLoopClause(self, ctx: ACSLParser.LoopClauseContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#clauseKind.
    def visitClauseKind(self, ctx: ACSLParser.ClauseKindContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#loopInvariant.
    def visitLoopInvariant(self, ctx: ACSLParser.LoopInvariantContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#loopAssigns.
    def visitLoopAssigns(self, ctx: ACSLParser.LoopAssignsContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#loopBehavior.
    def visitLoopBehavior(self, ctx: ACSLParser.LoopBehaviorContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#loopVariant.
    def visitLoopVariant(self, ctx: ACSLParser.LoopVariantContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#constant.
    def visitConstant(self, ctx: ACSLParser.ConstantContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#cExternalDeclaration.
    def visitCExternalDeclaration(self, ctx: ACSLParser.CExternalDeclarationContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#logicDef.
    def visitLogicDef(self, ctx: ACSLParser.LogicDefContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#typeVar.
    def visitTypeVar(self, ctx: ACSLParser.TypeVarContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#typeExpr.
    def visitTypeExpr(self, ctx: ACSLParser.TypeExprContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#polyId.
    def visitPolyId(self, ctx: ACSLParser.PolyIdContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#logicConstDef.
    def visitLogicConstDef(self, ctx: ACSLParser.LogicConstDefContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#logicFunctionDef.
    def visitLogicFunctionDef(self, ctx: ACSLParser.LogicFunctionDefContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#logicPredicateDef.
    def visitLogicPredicateDef(self, ctx: ACSLParser.LogicPredicateDefContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#parameters.
    def visitParameters(self, ctx: ACSLParser.ParametersContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#parameter.
    def visitParameter(self, ctx: ACSLParser.ParameterContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#lemmaDef.
    def visitLemmaDef(self, ctx: ACSLParser.LemmaDefContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#inductiveDef.
    def visitInductiveDef(self, ctx: ACSLParser.InductiveDefContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#indcase.
    def visitIndcase(self, ctx: ACSLParser.IndcaseContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#axiomaticDecl.
    def visitAxiomaticDecl(self, ctx: ACSLParser.AxiomaticDeclContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#logicDecl.
    def visitLogicDecl(self, ctx: ACSLParser.LogicDeclContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#logicTypeDecl.
    def visitLogicTypeDecl(self, ctx: ACSLParser.LogicTypeDeclContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#logicType.
    def visitLogicType(self, ctx: ACSLParser.LogicTypeContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#logicConstDecl.
    def visitLogicConstDecl(self, ctx: ACSLParser.LogicConstDeclContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#logicFunctionDecl.
    def visitLogicFunctionDecl(self, ctx: ACSLParser.LogicFunctionDeclContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#logicPredicateDecl.
    def visitLogicPredicateDecl(self, ctx: ACSLParser.LogicPredicateDeclContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#axiomDef.
    def visitAxiomDef(self, ctx: ACSLParser.AxiomDefContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#readsClause.
    def visitReadsClause(self, ctx: ACSLParser.ReadsClauseContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#id.
    def visitId(self, ctx: ACSLParser.IdContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#labelBinders.
    def visitLabelBinders(self, ctx: ACSLParser.LabelBindersContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#labelId.
    def visitLabelId(self, ctx: ACSLParser.LabelIdContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#ghostCode.
    def visitGhostCode(self, ctx: ACSLParser.GhostCodeContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by ACSLParser#acsl.
    def visitAcsl(self, ctx: ACSLParser.AcslContext):
        return self.visitChildren(ctx)


del ACSLParser
