from src.spec.ACSLLexer import ACSLLexer
from src.spec.ACSLParser import ACSLParser
from src.spec.ACSLParserVisitor import ACSLParserVisitor
from antlr4 import InputStream, CommonTokenStream


class SinkMeet(Exception):
    def __init__(self, message, fn_name):
        self.message = message
        self.fn_name = fn_name


class Taint2Sink(ACSLParserVisitor):
    """
    Binders in `forall` or `exists` predicates are regarded as taints.
    The i-th parameter of logic function/predicate call is regarded as the sink if it is of slice type(e.g. `&[i32]`).
    """

    def __init__(self):
        super().__init__()
        # store the functions which have sinks.
        self.logic_func_slice_params = {}
        self.taints = []

    def get_in_sink_binders(self, logic_func_slice_params, quantified_pred_ctx):
        self.logic_func_slice_params = logic_func_slice_params
        self.taints = []
        self.in_sink_binders = []
        for binder in quantified_pred_ctx.binder():
            self.visitBinder(binder)
        self.visitPred(quantified_pred_ctx.pred()[0])

        return self.in_sink_binders.copy()

    def visitBinder(self, ctx):
        if ctx.logicAtomicType().getText() == "int*":
            for term in ctx.term():
                self.taints.append(term.getText())
        return super().visitBinder(ctx)

    def visitPolyId(self, ctx):
        if self.logic_func_slice_params.get(ctx.getText().strip()) is not None:
            raise SinkMeet("SinkMeet", ctx.getText())
        return super().visitPolyId(ctx)

    def visitTerm(self, ctx):
        if ctx.polyId():
            try:
                self.visitPolyId(ctx.polyId())
            except SinkMeet as e:
                for idx, term in enumerate(ctx.term()):
                    if idx in self.logic_func_slice_params.get(e.fn_name):
                        if term.getText() in self.taints:
                            self.in_sink_binders.append(term.getText())
                return None
        return super().visitTerm(ctx)
