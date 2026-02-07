parser grammar ACSLParser;

options {
	tokenVocab = ACSLLexer;
}

logicParaVar:
	logicAtomicType IDENT
	| 'struct' IDENT IDENT
	| logicAtomicType '[' ']' IDENT;

logicAtomicType: 'integer' | 'real' | 'boolean' | 'size_t' | 'int' | 'unsigned' | 'int*'| 'char' | 'char*';


/* annotation */
logicConstant:
	INT_CONSTANT
	| FLOAT_CONSTANT
	| '\\true'
	| '\\false'
	| CHAR_CONSTANT;

term:
	IDENT
	| '\\result'
	| '\\old' '(' term ')'					
	| logicConstant	
	| '{' term '\\with' '[' term ']' '=' term '}'
	| '(' term ')'
	| term '[' term ']'
	| term '.' IDENT
	| term '->' IDENT
	| '-' term
	| term ('*' | '/' | '%') term
	| term ('+' | '-') term
	| '*' term
	| '&' term
	| polyId '(' term (',' term)* ')'
	| '\\abs' '(' term ')'
	| '\\at' '(' term ',' IDENT ')'
	| '\\at' '(' tset ',' IDENT ')'
	| '{' term (',' term)* '}'
	| term '==' NULL
	| term '!=' NULL
	| term ('<' | '<=' | '>' | '>=') term	
	| term ('==' | '!=') term				
	| term '&&' term						
	| term '||' term
	| term '?' term ':' term;						

pred:
	'\\true'
	| '\\false'
	| term 
	| term '==' NULL
	| term '!=' NULL
	| term (
		('<' | '<=' | '>' | '>=' | '==' | '!=') term
	)+	
	| IDENT ('(' term (',' term)* ')')?
	| '(' pred ')'
	| pred '&&' pred
	| pred '||' pred
	| <assoc=right> pred '==>' pred
	| '\\result'
	| <assoc=right> pred '<==>' pred
	| '!' pred
	| pred '^^' pred
	| '\\valid' '(' IDENT '+' '(' term '..' term ')' ')'
	| '\\valid' '(' location ')'
	| '\\valid_read' '(' IDENT '+' '(' term '..' term ')' ')'
	| '\\valid_read' '(' location ')'
	| '\\separated' '(' location ',' locationsList ')'
	| ('\\forall' | '\\exists') binder (',' binder)* ';' pred
	| '\\old' '(' pred ')'
	| '\\subset' '(' tset ',' tset ')'
	| term '\\in' tset
	| IDENT ':' pred;

binder: logicAtomicType term (',' term)*;

// 2.3 Function contracts
funcContract:
    '/*@' 
    requiresClause* 
    terminatesClause?
    decreasesClause?
    simpleClause* 
    namedBehavior* 
    completenessClause* 
    '*/'
  | '//@' 
    requiresClause* 
    terminatesClause?
    decreasesClause?
    simpleClause* 
    namedBehavior* 
    completenessClause*;

simpleClause: 
	assignsClause 
	| ensuresClause;

terminatesClause:  'terminates' pred  ';';

assignsClause: 'assigns' locations ';';

locations: 
	locationsList 
	| '\\nothing';

locationsList: location (',' location)*;

location: tset;

requiresClause: 'requires' pred ';';

decreasesClause:
	'decreases' (term | '(' term (',' term)+ ')') ';';

ensuresClause: 'ensures' pred ';';

namedBehavior: 'behavior' IDENT ':' behaviorBody;

behaviorBody: assumesClause* requiresClause* simpleClause*;

assumesClause: 'assumes' pred ';';

completenessClause:
	'complete behaviors' (IDENT (',' IDENT)*)? ';'
	| 'disjoint behaviors' (IDENT (',' IDENT)*)? ';';

// 2.3.4 Memory locations and sets of values
tset: '\\empty'
	| tset '->' IDENT
	| tset '.' IDENT
	| '*' tset
	| '&' tset
	| tset '[' tset ']'
	| tset '[' range ']'
	| '(' range ')'
	| '\\union' '(' tset (',' tset)* ')'
	| '\\inter' '(' tset (',' tset)* ')'
	| tset '+' tset
	| '(' tset ')'
	| '{' ( term (',' term)*)? '}'
	| term;


range: term? '..' term?;

// 2.4.1 Assertions
assertion:
	'/*@' 'assert' pred ';' '*/'
	| '//@' 'assert' pred ';'
	| '/*@' 'for' IDENT (',' IDENT)* ':' 'assert' pred ';' '*/'
	| '//@' 'for' IDENT (',' IDENT)* ':' 'assert' pred ';';

// 2.4.2 Loop annotationss
cStatement: 
	'/*@' loopAnnot '*/'
	| '//@' loopAnnot
	| assertion;

loopAnnot: 
	loopClause* loopBehavior* loopVariant?;

loopClause: 
	loopInvariant
	| loopAssigns;

clauseKind: 
	'check'
	| 'admit';

loopInvariant: clauseKind? 'loop' 'invariant' pred ';';

loopAssigns: 'loop' 'assigns' locations ';';

loopBehavior: 'for' IDENT (',' IDENT)* ':' loopClause+;

loopVariant: 
	'loop' 'variant' (term | '(' term (',' term)+ ')') ';';

constant: INT_CONSTANT | FLOAT_CONSTANT | 'true' | 'false';

// 2.6 Logic specifications
// Grammar for global logic definitions
cExternalDeclaration: 
	'/*@' logicDef+ '*/'
	| '//@' logicDef+;

logicDef: 
	logicConstDef
	| logicFunctionDef
	| logicPredicateDef
	| lemmaDef
	| inductiveDef
	| axiomaticDecl;

//typeVar: IDENT;
typeVar: 
	logicAtomicType
	| 'struct' IDENT
	| logicAtomicType '[' ']';

typeExpr: typeVar;


// polyId: IDENT typeVarBinders?;
polyId: id;

logicConstDef: 'logic' typeExpr polyId '=' term ';';

// logicFunctionDef: 'logic' typeExpr polyId parameters readsClause? '=' term ';';
logicFunctionDef: 'logic' typeExpr polyId parameters '=' term ';';

// logicPredicateDef: 'predicate' polyId parameters? readsClause? '=' pred ';';
logicPredicateDef: 'predicate' polyId parameters? '=' pred ';';

parameters: '(' parameter (',' parameter)* ')';

parameter: 
	typeExpr IDENT
	|typeExpr '*' IDENT;

lemmaDef: clauseKind? 'lemma' polyId ':' pred ';';

// 2.6.3 Inductive predicates
inductiveDef:
	'inductive' polyId parameters? '{' indcase* '}';

indcase: 'case' polyId ':' pred ';';

// 2.6.4 Axiomatic definitions
axiomaticDecl: 'axiomatic' IDENT '{' logicDecl* '}';

logicDecl:
	logicDef
	| logicTypeDecl
	| logicConstDecl
	| logicPredicateDecl
	| logicFunctionDecl
	| axiomDef;

logicTypeDecl: 'type' logicType ';';

logicType: IDENT;

logicConstDecl: 'logic' typeExpr polyId ';';

logicFunctionDecl: 'logic' typeExpr polyId parameters readsClause? ';';

logicPredicateDecl: 'predicate' polyId parameters? readsClause? ';';

axiomDef: 'axiom' polyId ':' pred ';';

// 2.6.10 Memory footprint specifications: reads clause
readsClause: 'reads' locations;

// Figure 2.18
id: IDENT labelBinders?;

labelBinders: '{' labelId (',' labelId)* '}';

// Figure 2.12
labelId: IDENT;

// 2.12 Ghost variables and statements
ghostCode: 
	'/*@' 'ghost' .*? '*/'
	| '//@' 'ghost' .*?;

// support only a subset of acsl
acsl:
	funcContract
	| cStatement
	| cExternalDeclaration
	| ghostCode;