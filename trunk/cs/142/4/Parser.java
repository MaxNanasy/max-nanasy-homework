import java.io.*;
import java.util.*;

public class Parser
{
    public static int SYNTAX_ERROR = 0, SEMANTIC_ERROR = 1, 
        UNDEFINED_ERROR = 2, REDEFINED_ERROR = 3;
    
    
    private Scanner scanner;
    public int sym; //Stores the current input from getSym()
    private static FileOutputStream outFile;
    private static PrintStream fileData;
    String lexeme;

    private SymbolTable symbolTable;
    
    private void bind (SymbolTable table, String name, SymbolTable.Symbol symbol)
    {
	if (!table.bind (name, symbol))
	    printError (SEMANTIC_ERROR, REDEFINED_ERROR);
    }

    public SymbolTable.Symbol getBinding (SymbolTable table, String name, String type)
    {
	SymbolTable.Symbol symbol = table.getBinding (name, type);
	if (symbol == null)
	    printError (SEMANTIC_ERROR, UNDEFINED_ERROR);
	return symbol;
    }
    
    private void printError(int errorType, int symOrError)
    {
        //For Comparing Output: please use this format as it will be used
        //to compare output results
        fileData.println("Error: " + ((errorType == SYNTAX_ERROR)? "SYNTAX: "
                                      : "SEMANTIC: ") +
                         ((errorType == SYNTAX_ERROR)? Scanner.Terminal[symOrError] :
                          (symOrError == UNDEFINED_ERROR)? " UNDEFINED SYMBOL" : "REDEFINED SYMBOL"));
        
        symbolTable.printSymTable(fileData);

        System.err.println(" Error Encountered on Line Number: " +
                           Scanner.getLineNumber());
        System.exit(-1);
    }
    
    
    
    /* USED FOR PRINTING ERROR INFORMATION */
    private void printError(int symReceived)
    {
        printError(SYNTAX_ERROR, sym);
    }
    
    
    /* CONSTRUCTOR */
    
    public Parser(String args[])
    {
        scanner = new Scanner(args[0]);
	symbolTable = new SymbolTable ();

        try {
            outFile = new FileOutputStream(args[0]+".out");
            fileData = new PrintStream( outFile );
        }
        
        catch (IOException e) {
            e.printStackTrace();
            System.err.println("init: Errors accessing output file: "+args[0]+".out");
            System.exit(-2);
        }
        
        sym=Scanner.getSym(); //buffer the symbol input
    }
    
    /* PROGRAM FUNCTION */
    /*
     *
     program  =
     declarations
     procedureDeclarations
     _main _( _)_{
     declarations
     statementSequence
     _}
     
     * */
    public void program (SymbolTable table)
    {
        declarations(table);
        proceduredeclarations(table);
        expect(Scanner.MAIN);
        expect(Scanner.OPEN_PAREN);
        expect(Scanner.CLOSE_PAREN);
        expect(Scanner.OPEN_BRACE);
	SymbolTable.Symbol.SimplyTyped.Procedure main = new SymbolTable.Symbol.SimplyTyped.Procedure (SymbolTable.TypeDesignator.VOID, table);
	declarations (main.table);
	statementSequence (main.table);
        expect(Scanner.CLOSE_BRACE);
        expect(Scanner.END_OF);
	bind (table, "MAIN", main);
	main.table = null;
    }
    
    /**
       statementSequence  =  statement {statement}
       * */
    private void statementSequence(SymbolTable table)
    {
	if (! statement (table)) {
	    printError(sym);
	    return;
	}
	while (statement (table));
    }

    /**
       statement =  assignment | input | output | ifStatement | whileStatement | returnStatement | procedureStatement.
       * */
    private boolean statement (SymbolTable table) {
	switch (sym) {
	case Scanner.IDENT : assignment         (table); break;
	case Scanner.GET   : input              (table); break;
	case Scanner.PRINT : output             (table); break;
	case Scanner.IF    : ifStatement        (table); break;
	case Scanner.WHILE : whileStatement     (table); break;
	case Scanner.COLON : procedureStatement (table); break;
	case Scanner.RETURN: returnStatement    (table); break;
	default: return false;
	}
	return true;
    }

    // procedureStatement = procedureCall ;
    private void procedureStatement (SymbolTable table) {
	procedureCall (table);
	expect(Scanner.SEMI_COLON);
    }
    
    // procedureCall = :: ident  ( [parameters] )
    private Expression procedureCall (SymbolTable table) {
	expect (Scanner.COLON);
	expect (Scanner.COLON);
	String name = ident ();
	expect (Scanner.OPEN_PAREN);
	if (! accept (Scanner.CLOSE_PAREN)) {
	    List <Expression> arguments = parameters();
	    expect(Scanner.CLOSE_PAREN);
	    return new Expression.ProcedureCall (name, arguments);
	}
	else return new Expression.ProcedureCall (name, new LinkedList <Expression> ());
    }

    // returnStatement = _return  expression _;
    private void returnStatement (SymbolTable table) {
	expect (Scanner.RETURN);
	expression (table);
	expect (Scanner.SEMI_COLON);
    }
 
    // expression  =  term { ( + | - ) term }
    private Expression expression (SymbolTable table)
    {
	if (sym==(Scanner.IDENT)||sym==(Scanner.NUMBER)||sym==Scanner.COLON||sym==Scanner.OPEN_PAREN){
	    Expression expression = term (table);
	    while (accept(Scanner.PLUS) || accept(Scanner.MINUS)){
		expression = new Expression.BinaryOperation.Addition (expression, term (table));
	    }
	    return expression;
	}
	else {
	    printError(sym);
	    return null;
	}
    }
    
    // term  =  factor { (* | / ) factor}
    private Expression term(SymbolTable table)
    {
	if (sym==(Scanner.IDENT)||sym==(Scanner.NUMBER)||sym==Scanner.COLON||sym==Scanner.OPEN_PAREN) {
	    Expression expression = factor (table);
	    while (accept(Scanner.MULT_OP) || accept(Scanner.DIV)){
		expression = new Expression.BinaryOperation.Multiplication (expression, factor());
	    }
	    return expression;
	}
	else {
	    printError(sym);
	    return null;
	}
    }
    
    // factor  =  designator  |  number  | procedureCall |  _( expression _)
    private Expression factor (SymbolTable table) {
	switch (sym) {
	case Scanner.IDENT : return designator    ()                 ;
	case Scanner.NUMBER: return new Expression.Number (number ());
	case Scanner.COLON : return procedureCall (table)            ;
	case Scanner.OPEN_PAREN:
	    expect(Scanner.OPEN_PAREN);
	    Expression expression = expression (table);
	    expect(Scanner.CLOSE_PAREN);
	    return expression;
	default:
	    printError (sym);
	    return null;
	}
    }
    
    // designator = ident { [ expr ]}
    private Expression designator () {
	if (sym==Scanner.IDENT){
	    Expression.Designator designator = new Expression.Designator.Variable (ident ());
	    while (accept (Scanner.OPEN_BRKT)) {
		designator = new Expression.Designator.ArrayReference (designator, expression ());
		expect(Scanner.CLOSE_BRKT);
	    }
	    return designator;
	} else {
	    printError(sym);
	    return null;
	}
    }
    
    //whileStatement  =  _while condition _{ statementSequence  _}
    private void whileStatement (SymbolTable table) {
	expect (Scanner.WHILE);
	condition (table);
	expect(Scanner.OPEN_BRACE);
	statementSequence (table);
	expect(Scanner.CLOSE_BRACE);
    }

    //condition  =  ( expression ( _== |  _!=  |  _< |  _<=  |  _>  |  _>= ) expression  )
    private void condition (SymbolTable table) {
	expect(Scanner.OPEN_PAREN);
	expression (table);
	if ((! accept (Scanner.EQUAL))
	 && (! accept (Scanner.NOT_EQ))
	 && (! accept (Scanner.LESS_THAN))
	 && (! accept (Scanner.LESS_THAN_EQ))
	 && (! accept (Scanner.GRT_THAN))
	 && (! accept (Scanner.GRT_THAN_EQ))) {
	    printError(sym);
	    return;
	}
	expression ();
	expect(Scanner.CLOSE_PAREN);
    }
    
    
    /* ifStatement  =  _if condition _{ statementSequence  _}
       [  else_{ statementSequence  _} ] */

    private void ifStatement (SymbolTable table) {
	expect(Scanner.IF);
	condition (table);
	expect (Scanner.OPEN_BRACE);
	statementSequence (table);
	expect (Scanner.CLOSE_BRACE);
	if (accept (Scanner.ELSE)){
	    expect (Scanner.OPEN_BRACE);
	    statementSequence (table);
	    expect (Scanner.CLOSE_BRACE);
	}
    }
    
    
    // output = _print _( parameters _) _;
    private void output (SymbolTable table)
    {
	expect(Scanner.PRINT);
	expect(Scanner.OPEN_PAREN);
	parameters (table);
	expect(Scanner.CLOSE_PAREN);
	expect(Scanner.SEMI_COLON);
    }
    
    // input = _get _( parameters _) _;
    private void input (SymbolTable table)
    {
	expect(Scanner.GET);
	expect(Scanner.OPEN_PAREN);
	parameters (table);
	expect(Scanner.CLOSE_PAREN);
	expect(Scanner.SEMI_COLON);
    }
    
    /**
       assignment  =  designator _= expression _;
       * */
    private void assignment (SymbolTable table)
    {
	if (sym != Scanner.IDENT){
	    printError(sym);
	    return;
	}
	SymbolTable.TypeDesignator type0 = designator ().type (table);
	expect(Scanner.ASSIGN_OP);
	SymbolTable.TypeDesignator type1 = expression ().type (table);
	expect(Scanner.SEMI_COLON);
    }
    
    
    /**
       procedureDeclarations = {
       retType ident _( procedureFormalParams _) _{
       declarations
       statementSequence
       _}
       } **/
       
    private void proceduredeclarations(SymbolTable table) {
	// check for the empty case.
	if (sym==Scanner.IDENT || sym==Scanner.INT || sym==Scanner.SHORT || sym==Scanner.VOID){            
            while ((sym==Scanner.IDENT || sym==Scanner.INT || sym==Scanner.SHORT || sym==Scanner.VOID)){
		SymbolTable.TypeDesignator type = retType (table);
		SymbolTable.Symbol.SimplyTyped.Procedure procedure = new SymbolTable.Symbol.SimplyTyped.Procedure (type, table);
		bind (table, ident (), procedure);
		expect (Scanner.OPEN_PAREN);
		procedureFormalParams (procedure.table);
		expect (Scanner.CLOSE_PAREN);
		expect (Scanner.OPEN_BRACE);
		declarations (procedure.table);
		statementSequence (table);
		expect (Scanner.CLOSE_BRACE);
		procedure.table = null;
            }
	}
    }
    
    // procedureFormalParams = [ type [ _& ] ident {_, type [ _& ] ident }]
    private void procedureFormalParams(SymbolTable table) {
	if (nextIsType ()){
	    do {
		SymbolTable.TypeDesignator type = type (table);
		accept(Scanner.AMPERSAND);
		String name = ident();
		bind (table, name, new SymbolTable.Symbol.SimplyTyped.Variable (type));
	    } while (accept(Scanner.COMMA));
	}
    }
    

    private boolean nextIsType ()
    {
	return sym == Scanner.IDENT || sym == Scanner.INT || sym == Scanner.SHORT;
    }
	    
    
    // type = ident | int | short
    private SymbolTable.TypeDesignator type (SymbolTable table) {

	if (sym == Scanner.IDENT) {
	    String name = ident ();
	    getBinding (table, name, "TYPE").type ();
	    return new SymbolTable.TypeDesignator.Atomic (name);
	}
	else if (accept (Scanner.INT))   return SymbolTable.TypeDesignator.INT  ;
	else if (accept (Scanner.SHORT)) return SymbolTable.TypeDesignator.SHORT;
	else printError(sym);

	return null;

    }

    private String typeName (SymbolTable table)
    {

	if (sym == Scanner.IDENT) {
	    String name = ident ();
	    getBinding (table, name, "TYPE");
	    return name;
	} else if (accept (Scanner.INT)) return "INT"  ;
	else if (accept (Scanner.SHORT)) return "SHORT";
	else printError(sym);

	return null;

    }

    // retType = ident |  int  | short  | void
    private SymbolTable.TypeDesignator retType(SymbolTable table) {
	if (sym==(Scanner.IDENT)){
            return type (table);
	}
	else if (accept(Scanner.INT)){
	    return SymbolTable.TypeDesignator.INT;
	}
	else if (accept(Scanner.SHORT)){
	    return SymbolTable.TypeDesignator.SHORT;
	}
	else if (accept(Scanner.VOID)){
	    return SymbolTable.TypeDesignator.VOID;
	}
	else
            printError(sym);
	return null;
    }
    
    
    
    /**
     *
     declarations  = {
     _const    ident   _= number _;
     | _type   ident   _= newType _;
     |  _var   ident {_, ident } _:  newType _;
     }
     
    */
    
    private void declarations(SymbolTable table) {
        if (sym==Scanner.CONST||sym==Scanner.TYPE||sym==Scanner.VAR){
            while ((sym==Scanner.CONST||sym==Scanner.TYPE||sym==Scanner.VAR)){
                if (accept(Scanner.CONST)){
		    String name = ident ();
                    expect(Scanner.ASSIGN_OP);
                    SymbolTable.Symbol symbol = new SymbolTable.Symbol.Constant (number ());
                    expect(Scanner.SEMI_COLON);
		    bind (table, name, symbol);
                } else if (accept(Scanner.TYPE)){
                    String name = ident();
                    expect(Scanner.ASSIGN_OP);
                    SymbolTable.TypeDesignator type = newType (table);
                    expect(Scanner.SEMI_COLON);
		    bind (table, name, new SymbolTable.Symbol.SimplyTyped.Type (type));
                } else if (accept(Scanner.VAR)){
		    List <String> names = new LinkedList <String> ();
		    do names.add (ident ()); while (accept (Scanner.COMMA));
		    expect(Scanner.COLON);
                    SymbolTable.TypeDesignator type = newType (table);
                    expect(Scanner.SEMI_COLON);
		    for (String name : names) bind (table, name, new SymbolTable.Symbol.SimplyTyped.Variable (type));
                }
            }
        }
    }
    
    
    // newType  = type | _array number _of  type
    private SymbolTable.TypeDesignator newType (SymbolTable table) {
	if (accept (Scanner.ARRAY)) {
            short size = number ();
            expect (Scanner.OF);
            SymbolTable.TypeDesignator baseType = type (table);
	    return new SymbolTable.TypeDesignator.Array (baseType, size);
	} else
	    return type (table);
    }
        
    private short number() {
        if (expect(Scanner.NUMBER)){
        }
	return (short) Scanner.val;
    }
    
    private String ident() {
        if (expect(Scanner.IDENT)){
        }
	return lexeme;
    }
    
    
    // parameters = designator { _, designator}
    private List <Expression> parameters (SymbolTable table)
    {
	if (sym != Scanner.IDENT) {
	    printError (sym);
	    return null;
	}
	LinkedList <Expression> parameters = new LinkedList <Expression> ();
	do {
	    parameters.add (designator ());
	} while (accept (Scanner.COMMA));
	return parameters;
    }

    /**If you choose to use this design, you might want to look at Recursive_descent_parser in Wikipedia
     * Although you are welcome to use any other design you can think of. */
    private boolean accept(int s) {
        if (sym == s) {
            lexeme = Scanner.getLexeme();
            sym = Scanner.getSym();
            return true;
        }
        return false;
    }
    
    private boolean expect(int s) {
        lexeme = Scanner.getLexeme();
        if (accept(s))
            return true;
        printError(sym);
        return false;
    }    
    
    private class StudentInfo {
 	final static String ID       = "77672953"  ;
 	final static String Name     = "Max Nanasy";
 	final static String UCINetID = "mnanasy"   ;
    }
    
    
    public static void main(String[] args)
    {

        System.out.println(StudentInfo.ID);
        System.out.println(StudentInfo.Name);
        System.out.println(StudentInfo.UCINetID);
        Parser p = new Parser(args);

	p.bind (p.symbolTable, "int"  , new SymbolTable.Symbol.SimplyTyped.Type (SymbolTable.TypeDesignator.NULL));
	p.bind (p.symbolTable, "void" , new SymbolTable.Symbol.SimplyTyped.Type (SymbolTable.TypeDesignator.NULL));
	p.bind (p.symbolTable, "short", new SymbolTable.Symbol.SimplyTyped.Type (SymbolTable.TypeDesignator.NULL));
        
        p.program (p.symbolTable);

	p.symbolTable.printSymTable (fileData);

    }
    
}
