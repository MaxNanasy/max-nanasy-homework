package ebnf;

import static rule.Rule.Parseable.Constructor.*;
import static scanner.Scanner.*;
import rule.Rule.Parseable;
import rule.Rule.Parseable.Named;

public final class EBNF
{

    private static final Named
	  type                  = named ("type"                 )
	, retType               = named ("retType"              ) //(conjunct (terminal (IDENT), terminal (INT), terminal (SHORT), terminal (VOID)))
	, newType               = named ("newType"              ) //(conjunct (type, concat (terminal (ARRAY), terminal (NUMBER), terminal (OF), type)))
	, designator            = named ("designator"           ) //concat (terminal (IDENT), many (concat (terminal (OPEN_BRKT), expression, terminal (CLOSE_BRKT)))))
	, factor                = named ("factor"               ) //conjunct (designator, terminal (NUMBER), procedureCall, terminal (OPEN_PAREN), expression, terminal (CLOSE_PAREN)))
	, term                  = named ("term"                 ) //concat (factor, many (concat (conjunct (terminal (MULT_OP), terminal (DIV)), factor))))
	, expression            = named ("expression"           ) //concat (term, conjunct (terminal (PLUS), terminal (MINUS))))
	, parameters            = named ("parameters"           ) //concat (designator, many (concat (terminal (COMMA), designator))))
	, input                 = named ("input"                ) //concat (terminal (GET), terminal (OPEN_PAREN), parameters, terminal (CLOSE_PAREN)))
	, output                = named ("output"               ) //concat (terminal (PRINT), terminal (OPEN_PAREN), parameters, terminal (CLOSE_PAREN)))
	, condition             = named ("condition"            ) //concat (terminal (OPEN_PAREN), expression, conjunct (terminal (EQUAL), terminal (NOT_EQ), terminal (LESS_THAN), terminal (LESS_THAN_EQ), terminal (GRT_THAN), terminal (GRT_THAN_EQ)), expression, terminal (CLOSE_PAREN)))
	, returnStatement       = named ("returnStatement"      ) //concat (terminal (RETURN), expression, terminal (SEMI_COLON)))
	, procedureCall         = named ("procedureCall"        ) //concat (terminal (COLON), terminal (COLON), terminal (IDENT), terminal (OPEN_PAREN), optional (parameters), terminal (CLOSE_PAREN)))
	, procedureStatement    = named ("procedureStatement"   ) //concat (procedureCall, terminal (SEMI_COLON)))
	, ifStatement           = named ("ifStatement"          ) //concat (terminal (IF), condition, terminal (OPEN_BRACE), statementSequence, terminal (CLOSE_BRACE)))
	, whileStatement        = named ("whileStatement"       ) //concat (terminal (WHILE), condition, terminal (OPEN_BRACE), statementSequence, terminal (CLOSE_BRACE)))
	, declarations          = named ("declarations"         ) //many (conjunct (concat (terminal (CONST), terminal (IDENT), terminal (ASSIGN_OP), terminal (NUMBER), terminal (SEMI_COLON)), concat (terminal (TYPE), terminal (IDENT), terminal (ASSIGN_OP), newType, terminal (SEMI_COLON)), concat (terminal (VAR), terminal (IDENT), many (concat (terminal (COMMA), terminal (IDENT))), terminal (COLON), newType, terminal (SEMI_COLON)))))
	, procedureFormalParams = named ("procedureFormalParams") //optional (concat (type, optional (terminal (AMPERSAND)), terminal (IDENT), many (concat (terminal (COMMA), type, optional (terminal (AMPERSAND)), terminal (IDENT))))))
	, procedureDeclarations = named ("procedureDeclarations") //many (concat (retType, terminal (IDENT), terminal (OPEN_PAREN), procedureFormalParams, terminal (CLOSE_PAREN), terminal (OPEN_BRACE), declarations, statementSequence, terminal (CLOSE_BRACE))))
	, assignment            = named ("assignment"           ) //concat (designator, terminal (ASSIGN_OP), expression, terminal (SEMI_COLON)))
	, statement             = named ("statement"            ) //conjunct (assignment, input, output, ifStatement, whileStatement, returnStatement, procedureStatement))
	, statementSequence     = named ("statementSequence"    ) //many1 (statement));
	;

    //   private static Named sequence (Named name, void... things) { return name; }

    public  static final Named
	program               = named ("program", concat (declarations, procedureDeclarations, terminal (MAIN), terminal (OPEN_PAREN), terminal (CLOSE_PAREN), terminal (OPEN_BRACE), declarations, statementSequence, terminal (CLOSE_BRACE))); // type.associate (conjunct (terminal (IDENT), terminal (INT), terminal (SHORT))));

}
