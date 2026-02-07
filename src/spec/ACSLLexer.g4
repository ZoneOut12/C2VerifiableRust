lexer grammar ACSLLexer;

/* --- vstd --- */
ABS: '\\abs';

/* --- \at --- */
AT: '\\at';

/* --- \separated --- */
SEPARATED: '\\separated';
NULL: 'NULL';

/* --- ghost code --- */
GHOST: 'ghost';
GHOSTQualifier: '\\ghost';

/* --- reads clause --- */
READS: 'reads';

/* --- Logic specifications --- */
LOGIC: 'logic';
QUESTIONMARK: '?';
PREDICATE: 'predicate';
LEMMA: 'lemma';
INDUCTIVE: 'inductive';
CASE: 'case';
AXIOMATIC: 'axiomatic';
AXIOM: 'axiom';
TYPE: 'type';

/* --- literals --- */
VOID: 'void';
STRUCT: 'struct';

LPAR: '(';
RPAR: ')';
LBRACE: '{';
RBRACE: '}';
COMMA: ',';
SEMICOLON: ';';
LBRACKET: '[';
RBRACKET: ']';
PERIOD: '.';

/* --- TypeExpr --- */
INT: 'int';
FLOAT: 'float';
BOOL: 'bool';
SIZET: 'size_t';
UNSIGNED: 'unsigned';
INTPOINTER: 'int*';
CHAR: 'char';
CHARPOINTER: 'char*';

IF: 'if';
ELSE: 'else';
BREAK: 'break';
CONTINUE: 'continue';
RETURN: 'return';
WHILE: 'while';
DO: 'do';
FOR: 'for';

ASSIGN: '=';

EQ: '==';
NE: '!=';
LE: '<=';
LT: '<';
GE: '>=';
GT: '>';
ADD: '+';
MINUS: '-';
MUL: '*';
DIV: '/';
NEG: '!';
MOD: '%';
AND: '&&';
OR: '||';
EXPR_TRUE: 'true';
EXPR_FALSE: 'false';

ANNO_TRUE: '\\true';
ANNO_FALSE: '\\false';
RESULT: '\\result';
LENGTH: '\\length';
OLD: '\\old';
WITH: '\\with';
IMPLY: '==>';
EQUIV: '<==>';
XOR: '^^';
FORALL: '\\forall';
EXISTS: '\\exists';
BOOLEAN: 'boolean';
INTEGER: 'integer';
REAL: 'real';
REQUIRES: 'requires';
DECREASES: 'decreases';
ENSURES: 'ensures';
ASSERT: 'assert';
LOOP: 'loop';
INVARIANT: 'invariant';
VARIANT: 'variant';
VALID: '\\valid';
VALIDREAD: '\\valid_read';
APOSTROPHE: '..';

/* --- others related with ACSL --- */
CHECK: 'check';
ADMIT: 'admit';
ASSIGNS: 'assigns';
TERMINATES: 'terminates';
BEHAVIOR: 'behavior';
COLON: ':';
ASSUMES: 'assumes';
COMPLETE_BEHAVIOR: 'complete behaviors';
DISJOINT_BEHAVIOR: 'disjoint behaviors';
EMPTY_SET: '\\empty';
BIT_AND: '&';
UNION: '\\union';
INTER: '\\inter';
ARROW: '->';
SUBSET: '\\subset';
IN: '\\in';
NOTHING: '\\nothing';

/* --- constants --- */
INT_CONSTANT
  : '0x' [0-9a-fA-F]+
  | [0-9]+
  ;
FLOAT_CONSTANT: [0-9]+ '.' [0-9]+;
IDENT: [a-zA-Z] [a-zA-Z0-9_]*;
CHAR_CONSTANT: '\'' ESCAPED_CHAR '\'';

fragment ESCAPED_CHAR
  : '\\n'       // newline
  | '\\t'       // tab
  | '\\r'       // carriage return
  | '\\b'       // backspace
  | '\\f'       // form feed
  | '\\0'       // null
  | '\\\\'      // backslash
  | '\u0020'..'\u007E' // printable ASCII (space to ~)
  ;

/* --- comments --- */
COMMENT: '/*' ('*/' | ~('@') .*? '*/') -> skip;
LINE_COMMENT: '//' ([\r\n] | ~('@') ~[\r\n]*) -> skip;

/* --- annotationss --- */
ANNOT_START: '/*@';
ANNOT_END: '*/';
LINE_ANNOT_START: '//@';

/* --- '@' is skipped in annotation --- */
ATE: '@';

/* --- LINEEND cannot be skipped for line annotation --- */
LINEEND: [\r\n] -> skip;

/* --- skip white spaces --- */
WS: [ \t\u000C] -> skip;