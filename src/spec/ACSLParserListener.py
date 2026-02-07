# Generated from ACSLParser.g4 by ANTLR 4.13.2
from antlr4 import *

if "." in __name__:
    from .ACSLParser import ACSLParser
else:
    from ACSLParser import ACSLParser


# This class defines a complete listener for a parse tree produced by ACSLParser.
class ACSLParserListener(ParseTreeListener):

    # Enter a parse tree produced by ACSLParser#logicParaVar.
    def enterLogicParaVar(self, ctx: ACSLParser.LogicParaVarContext):
        pass

    # Exit a parse tree produced by ACSLParser#logicParaVar.
    def exitLogicParaVar(self, ctx: ACSLParser.LogicParaVarContext):
        pass

    # Enter a parse tree produced by ACSLParser#logicAtomicType.
    def enterLogicAtomicType(self, ctx: ACSLParser.LogicAtomicTypeContext):
        pass

    # Exit a parse tree produced by ACSLParser#logicAtomicType.
    def exitLogicAtomicType(self, ctx: ACSLParser.LogicAtomicTypeContext):
        pass

    # Enter a parse tree produced by ACSLParser#logicConstant.
    def enterLogicConstant(self, ctx: ACSLParser.LogicConstantContext):
        pass

    # Exit a parse tree produced by ACSLParser#logicConstant.
    def exitLogicConstant(self, ctx: ACSLParser.LogicConstantContext):
        pass

    # Enter a parse tree produced by ACSLParser#term.
    def enterTerm(self, ctx: ACSLParser.TermContext):
        pass

    # Exit a parse tree produced by ACSLParser#term.
    def exitTerm(self, ctx: ACSLParser.TermContext):
        pass

    # Enter a parse tree produced by ACSLParser#pred.
    def enterPred(self, ctx: ACSLParser.PredContext):
        pass

    # Exit a parse tree produced by ACSLParser#pred.
    def exitPred(self, ctx: ACSLParser.PredContext):
        pass

    # Enter a parse tree produced by ACSLParser#binder.
    def enterBinder(self, ctx: ACSLParser.BinderContext):
        pass

    # Exit a parse tree produced by ACSLParser#binder.
    def exitBinder(self, ctx: ACSLParser.BinderContext):
        pass

    # Enter a parse tree produced by ACSLParser#funcContract.
    def enterFuncContract(self, ctx: ACSLParser.FuncContractContext):
        pass

    # Exit a parse tree produced by ACSLParser#funcContract.
    def exitFuncContract(self, ctx: ACSLParser.FuncContractContext):
        pass

    # Enter a parse tree produced by ACSLParser#simpleClause.
    def enterSimpleClause(self, ctx: ACSLParser.SimpleClauseContext):
        pass

    # Exit a parse tree produced by ACSLParser#simpleClause.
    def exitSimpleClause(self, ctx: ACSLParser.SimpleClauseContext):
        pass

    # Enter a parse tree produced by ACSLParser#terminatesClause.
    def enterTerminatesClause(self, ctx: ACSLParser.TerminatesClauseContext):
        pass

    # Exit a parse tree produced by ACSLParser#terminatesClause.
    def exitTerminatesClause(self, ctx: ACSLParser.TerminatesClauseContext):
        pass

    # Enter a parse tree produced by ACSLParser#assignsClause.
    def enterAssignsClause(self, ctx: ACSLParser.AssignsClauseContext):
        pass

    # Exit a parse tree produced by ACSLParser#assignsClause.
    def exitAssignsClause(self, ctx: ACSLParser.AssignsClauseContext):
        pass

    # Enter a parse tree produced by ACSLParser#locations.
    def enterLocations(self, ctx: ACSLParser.LocationsContext):
        pass

    # Exit a parse tree produced by ACSLParser#locations.
    def exitLocations(self, ctx: ACSLParser.LocationsContext):
        pass

    # Enter a parse tree produced by ACSLParser#locationsList.
    def enterLocationsList(self, ctx: ACSLParser.LocationsListContext):
        pass

    # Exit a parse tree produced by ACSLParser#locationsList.
    def exitLocationsList(self, ctx: ACSLParser.LocationsListContext):
        pass

    # Enter a parse tree produced by ACSLParser#location.
    def enterLocation(self, ctx: ACSLParser.LocationContext):
        pass

    # Exit a parse tree produced by ACSLParser#location.
    def exitLocation(self, ctx: ACSLParser.LocationContext):
        pass

    # Enter a parse tree produced by ACSLParser#requiresClause.
    def enterRequiresClause(self, ctx: ACSLParser.RequiresClauseContext):
        pass

    # Exit a parse tree produced by ACSLParser#requiresClause.
    def exitRequiresClause(self, ctx: ACSLParser.RequiresClauseContext):
        pass

    # Enter a parse tree produced by ACSLParser#decreasesClause.
    def enterDecreasesClause(self, ctx: ACSLParser.DecreasesClauseContext):
        pass

    # Exit a parse tree produced by ACSLParser#decreasesClause.
    def exitDecreasesClause(self, ctx: ACSLParser.DecreasesClauseContext):
        pass

    # Enter a parse tree produced by ACSLParser#ensuresClause.
    def enterEnsuresClause(self, ctx: ACSLParser.EnsuresClauseContext):
        pass

    # Exit a parse tree produced by ACSLParser#ensuresClause.
    def exitEnsuresClause(self, ctx: ACSLParser.EnsuresClauseContext):
        pass

    # Enter a parse tree produced by ACSLParser#namedBehavior.
    def enterNamedBehavior(self, ctx: ACSLParser.NamedBehaviorContext):
        pass

    # Exit a parse tree produced by ACSLParser#namedBehavior.
    def exitNamedBehavior(self, ctx: ACSLParser.NamedBehaviorContext):
        pass

    # Enter a parse tree produced by ACSLParser#behaviorBody.
    def enterBehaviorBody(self, ctx: ACSLParser.BehaviorBodyContext):
        pass

    # Exit a parse tree produced by ACSLParser#behaviorBody.
    def exitBehaviorBody(self, ctx: ACSLParser.BehaviorBodyContext):
        pass

    # Enter a parse tree produced by ACSLParser#assumesClause.
    def enterAssumesClause(self, ctx: ACSLParser.AssumesClauseContext):
        pass

    # Exit a parse tree produced by ACSLParser#assumesClause.
    def exitAssumesClause(self, ctx: ACSLParser.AssumesClauseContext):
        pass

    # Enter a parse tree produced by ACSLParser#completenessClause.
    def enterCompletenessClause(self, ctx: ACSLParser.CompletenessClauseContext):
        pass

    # Exit a parse tree produced by ACSLParser#completenessClause.
    def exitCompletenessClause(self, ctx: ACSLParser.CompletenessClauseContext):
        pass

    # Enter a parse tree produced by ACSLParser#tset.
    def enterTset(self, ctx: ACSLParser.TsetContext):
        pass

    # Exit a parse tree produced by ACSLParser#tset.
    def exitTset(self, ctx: ACSLParser.TsetContext):
        pass

    # Enter a parse tree produced by ACSLParser#range.
    def enterRange(self, ctx: ACSLParser.RangeContext):
        pass

    # Exit a parse tree produced by ACSLParser#range.
    def exitRange(self, ctx: ACSLParser.RangeContext):
        pass

    # Enter a parse tree produced by ACSLParser#assertion.
    def enterAssertion(self, ctx: ACSLParser.AssertionContext):
        pass

    # Exit a parse tree produced by ACSLParser#assertion.
    def exitAssertion(self, ctx: ACSLParser.AssertionContext):
        pass

    # Enter a parse tree produced by ACSLParser#cStatement.
    def enterCStatement(self, ctx: ACSLParser.CStatementContext):
        pass

    # Exit a parse tree produced by ACSLParser#cStatement.
    def exitCStatement(self, ctx: ACSLParser.CStatementContext):
        pass

    # Enter a parse tree produced by ACSLParser#loopAnnot.
    def enterLoopAnnot(self, ctx: ACSLParser.LoopAnnotContext):
        pass

    # Exit a parse tree produced by ACSLParser#loopAnnot.
    def exitLoopAnnot(self, ctx: ACSLParser.LoopAnnotContext):
        pass

    # Enter a parse tree produced by ACSLParser#loopClause.
    def enterLoopClause(self, ctx: ACSLParser.LoopClauseContext):
        pass

    # Exit a parse tree produced by ACSLParser#loopClause.
    def exitLoopClause(self, ctx: ACSLParser.LoopClauseContext):
        pass

    # Enter a parse tree produced by ACSLParser#clauseKind.
    def enterClauseKind(self, ctx: ACSLParser.ClauseKindContext):
        pass

    # Exit a parse tree produced by ACSLParser#clauseKind.
    def exitClauseKind(self, ctx: ACSLParser.ClauseKindContext):
        pass

    # Enter a parse tree produced by ACSLParser#loopInvariant.
    def enterLoopInvariant(self, ctx: ACSLParser.LoopInvariantContext):
        pass

    # Exit a parse tree produced by ACSLParser#loopInvariant.
    def exitLoopInvariant(self, ctx: ACSLParser.LoopInvariantContext):
        pass

    # Enter a parse tree produced by ACSLParser#loopAssigns.
    def enterLoopAssigns(self, ctx: ACSLParser.LoopAssignsContext):
        pass

    # Exit a parse tree produced by ACSLParser#loopAssigns.
    def exitLoopAssigns(self, ctx: ACSLParser.LoopAssignsContext):
        pass

    # Enter a parse tree produced by ACSLParser#loopBehavior.
    def enterLoopBehavior(self, ctx: ACSLParser.LoopBehaviorContext):
        pass

    # Exit a parse tree produced by ACSLParser#loopBehavior.
    def exitLoopBehavior(self, ctx: ACSLParser.LoopBehaviorContext):
        pass

    # Enter a parse tree produced by ACSLParser#loopVariant.
    def enterLoopVariant(self, ctx: ACSLParser.LoopVariantContext):
        pass

    # Exit a parse tree produced by ACSLParser#loopVariant.
    def exitLoopVariant(self, ctx: ACSLParser.LoopVariantContext):
        pass

    # Enter a parse tree produced by ACSLParser#constant.
    def enterConstant(self, ctx: ACSLParser.ConstantContext):
        pass

    # Exit a parse tree produced by ACSLParser#constant.
    def exitConstant(self, ctx: ACSLParser.ConstantContext):
        pass

    # Enter a parse tree produced by ACSLParser#cExternalDeclaration.
    def enterCExternalDeclaration(self, ctx: ACSLParser.CExternalDeclarationContext):
        pass

    # Exit a parse tree produced by ACSLParser#cExternalDeclaration.
    def exitCExternalDeclaration(self, ctx: ACSLParser.CExternalDeclarationContext):
        pass

    # Enter a parse tree produced by ACSLParser#logicDef.
    def enterLogicDef(self, ctx: ACSLParser.LogicDefContext):
        pass

    # Exit a parse tree produced by ACSLParser#logicDef.
    def exitLogicDef(self, ctx: ACSLParser.LogicDefContext):
        pass

    # Enter a parse tree produced by ACSLParser#typeVar.
    def enterTypeVar(self, ctx: ACSLParser.TypeVarContext):
        pass

    # Exit a parse tree produced by ACSLParser#typeVar.
    def exitTypeVar(self, ctx: ACSLParser.TypeVarContext):
        pass

    # Enter a parse tree produced by ACSLParser#typeExpr.
    def enterTypeExpr(self, ctx: ACSLParser.TypeExprContext):
        pass

    # Exit a parse tree produced by ACSLParser#typeExpr.
    def exitTypeExpr(self, ctx: ACSLParser.TypeExprContext):
        pass

    # Enter a parse tree produced by ACSLParser#polyId.
    def enterPolyId(self, ctx: ACSLParser.PolyIdContext):
        pass

    # Exit a parse tree produced by ACSLParser#polyId.
    def exitPolyId(self, ctx: ACSLParser.PolyIdContext):
        pass

    # Enter a parse tree produced by ACSLParser#logicConstDef.
    def enterLogicConstDef(self, ctx: ACSLParser.LogicConstDefContext):
        pass

    # Exit a parse tree produced by ACSLParser#logicConstDef.
    def exitLogicConstDef(self, ctx: ACSLParser.LogicConstDefContext):
        pass

    # Enter a parse tree produced by ACSLParser#logicFunctionDef.
    def enterLogicFunctionDef(self, ctx: ACSLParser.LogicFunctionDefContext):
        pass

    # Exit a parse tree produced by ACSLParser#logicFunctionDef.
    def exitLogicFunctionDef(self, ctx: ACSLParser.LogicFunctionDefContext):
        pass

    # Enter a parse tree produced by ACSLParser#logicPredicateDef.
    def enterLogicPredicateDef(self, ctx: ACSLParser.LogicPredicateDefContext):
        pass

    # Exit a parse tree produced by ACSLParser#logicPredicateDef.
    def exitLogicPredicateDef(self, ctx: ACSLParser.LogicPredicateDefContext):
        pass

    # Enter a parse tree produced by ACSLParser#parameters.
    def enterParameters(self, ctx: ACSLParser.ParametersContext):
        pass

    # Exit a parse tree produced by ACSLParser#parameters.
    def exitParameters(self, ctx: ACSLParser.ParametersContext):
        pass

    # Enter a parse tree produced by ACSLParser#parameter.
    def enterParameter(self, ctx: ACSLParser.ParameterContext):
        pass

    # Exit a parse tree produced by ACSLParser#parameter.
    def exitParameter(self, ctx: ACSLParser.ParameterContext):
        pass

    # Enter a parse tree produced by ACSLParser#lemmaDef.
    def enterLemmaDef(self, ctx: ACSLParser.LemmaDefContext):
        pass

    # Exit a parse tree produced by ACSLParser#lemmaDef.
    def exitLemmaDef(self, ctx: ACSLParser.LemmaDefContext):
        pass

    # Enter a parse tree produced by ACSLParser#inductiveDef.
    def enterInductiveDef(self, ctx: ACSLParser.InductiveDefContext):
        pass

    # Exit a parse tree produced by ACSLParser#inductiveDef.
    def exitInductiveDef(self, ctx: ACSLParser.InductiveDefContext):
        pass

    # Enter a parse tree produced by ACSLParser#indcase.
    def enterIndcase(self, ctx: ACSLParser.IndcaseContext):
        pass

    # Exit a parse tree produced by ACSLParser#indcase.
    def exitIndcase(self, ctx: ACSLParser.IndcaseContext):
        pass

    # Enter a parse tree produced by ACSLParser#axiomaticDecl.
    def enterAxiomaticDecl(self, ctx: ACSLParser.AxiomaticDeclContext):
        pass

    # Exit a parse tree produced by ACSLParser#axiomaticDecl.
    def exitAxiomaticDecl(self, ctx: ACSLParser.AxiomaticDeclContext):
        pass

    # Enter a parse tree produced by ACSLParser#logicDecl.
    def enterLogicDecl(self, ctx: ACSLParser.LogicDeclContext):
        pass

    # Exit a parse tree produced by ACSLParser#logicDecl.
    def exitLogicDecl(self, ctx: ACSLParser.LogicDeclContext):
        pass

    # Enter a parse tree produced by ACSLParser#logicTypeDecl.
    def enterLogicTypeDecl(self, ctx: ACSLParser.LogicTypeDeclContext):
        pass

    # Exit a parse tree produced by ACSLParser#logicTypeDecl.
    def exitLogicTypeDecl(self, ctx: ACSLParser.LogicTypeDeclContext):
        pass

    # Enter a parse tree produced by ACSLParser#logicType.
    def enterLogicType(self, ctx: ACSLParser.LogicTypeContext):
        pass

    # Exit a parse tree produced by ACSLParser#logicType.
    def exitLogicType(self, ctx: ACSLParser.LogicTypeContext):
        pass

    # Enter a parse tree produced by ACSLParser#logicConstDecl.
    def enterLogicConstDecl(self, ctx: ACSLParser.LogicConstDeclContext):
        pass

    # Exit a parse tree produced by ACSLParser#logicConstDecl.
    def exitLogicConstDecl(self, ctx: ACSLParser.LogicConstDeclContext):
        pass

    # Enter a parse tree produced by ACSLParser#logicFunctionDecl.
    def enterLogicFunctionDecl(self, ctx: ACSLParser.LogicFunctionDeclContext):
        pass

    # Exit a parse tree produced by ACSLParser#logicFunctionDecl.
    def exitLogicFunctionDecl(self, ctx: ACSLParser.LogicFunctionDeclContext):
        pass

    # Enter a parse tree produced by ACSLParser#logicPredicateDecl.
    def enterLogicPredicateDecl(self, ctx: ACSLParser.LogicPredicateDeclContext):
        pass

    # Exit a parse tree produced by ACSLParser#logicPredicateDecl.
    def exitLogicPredicateDecl(self, ctx: ACSLParser.LogicPredicateDeclContext):
        pass

    # Enter a parse tree produced by ACSLParser#axiomDef.
    def enterAxiomDef(self, ctx: ACSLParser.AxiomDefContext):
        pass

    # Exit a parse tree produced by ACSLParser#axiomDef.
    def exitAxiomDef(self, ctx: ACSLParser.AxiomDefContext):
        pass

    # Enter a parse tree produced by ACSLParser#readsClause.
    def enterReadsClause(self, ctx: ACSLParser.ReadsClauseContext):
        pass

    # Exit a parse tree produced by ACSLParser#readsClause.
    def exitReadsClause(self, ctx: ACSLParser.ReadsClauseContext):
        pass

    # Enter a parse tree produced by ACSLParser#id.
    def enterId(self, ctx: ACSLParser.IdContext):
        pass

    # Exit a parse tree produced by ACSLParser#id.
    def exitId(self, ctx: ACSLParser.IdContext):
        pass

    # Enter a parse tree produced by ACSLParser#labelBinders.
    def enterLabelBinders(self, ctx: ACSLParser.LabelBindersContext):
        pass

    # Exit a parse tree produced by ACSLParser#labelBinders.
    def exitLabelBinders(self, ctx: ACSLParser.LabelBindersContext):
        pass

    # Enter a parse tree produced by ACSLParser#labelId.
    def enterLabelId(self, ctx: ACSLParser.LabelIdContext):
        pass

    # Exit a parse tree produced by ACSLParser#labelId.
    def exitLabelId(self, ctx: ACSLParser.LabelIdContext):
        pass

    # Enter a parse tree produced by ACSLParser#ghostCode.
    def enterGhostCode(self, ctx: ACSLParser.GhostCodeContext):
        pass

    # Exit a parse tree produced by ACSLParser#ghostCode.
    def exitGhostCode(self, ctx: ACSLParser.GhostCodeContext):
        pass

    # Enter a parse tree produced by ACSLParser#acsl.
    def enterAcsl(self, ctx: ACSLParser.AcslContext):
        pass

    # Exit a parse tree produced by ACSLParser#acsl.
    def exitAcsl(self, ctx: ACSLParser.AcslContext):
        pass


del ACSLParser
