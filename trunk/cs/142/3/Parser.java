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
	declarations(main.table);
	bind (table, "MAIN", main);
        /**DO NOT UNCOMMENT
	   statementSequence();
        */
        expect(Scanner.CLOSE_BRACE);
        expect(Scanner.END_OF);
	main.table = null;
    }
    
    /**
       statementSequence  =  statement {statement}
       * */
    /**DO NOT UNCOMMENT
       private void statementSequence() {
       if (!statement(false)){
       printError(sym);
       return;
       }
       while (statement(true)){}
       }
    */
    /**
       statement =  assignment | input | output | ifStatement | whileStatement | returnStatement | procedureStatement.
       * */
    /**DO NOT UNCOMMENT
       private boolean statement(boolean perform) {
        
       if (sym==(Scanner.IDENT)){
       if (perform){
       assignment();
       }
       return true;
       }
       if (sym==(Scanner.GET)){
       if (perform){
       input();
       }
       return true;
       }
       if (sym==(Scanner.PRINT)){
       if (perform){
       output();
       }
       return true;
       }
       if (sym==(Scanner.IF)){
       if (perform){
       ifStatement();
       }
       return true;
       }
       if (sym==(Scanner.WHILE)){
       if (perform){
       whileStatement();
       }
       return true;
       }
       if (sym==(Scanner.COLON)){
       if (perform){
       procedureStatement();
       }
       return true;
       }
       if (sym==(Scanner.RETURN)){
       if (perform){
       returnStatement();
       }
       return true;
       }
       return false;
       }
    */    
    // procedureStatement = procedureCall ;
    /**DO NOT UNCOMMENT
       private void procedureStatement() {
       procedureCall();
       expect(Scanner.SEMI_COLON);
       }
    */
    
    // procedureCall = :: ident  ( [parameters] )
    /**DO NOT UNCOMMENT
       private void procedureCall() {
       expect(Scanner.COLON);
       expect(Scanner.COLON);
       ident();
       expect(Scanner.OPEN_PAREN);
       if (!accept(Scanner.CLOSE_PAREN)){
       parameters();
       expect(Scanner.CLOSE_PAREN);
       }
       }
    */    
    
    
    // returnStatement = _return  expression _;
    /**DO NOT UNCOMMENT
       private void returnStatement() {
       expect(Scanner.RETURN);
       expression();
       expect(Scanner.SEMI_COLON);
       }
    */
    
    // expression  =  term { ( + | - ) term }
    /**DO NOT UNCOMMENT
       private void expression() {
       if (sym==(Scanner.IDENT)||sym==(Scanner.NUMBER)||sym==Scanner.COLON||sym==Scanner.OPEN_PAREN){
       term();
       while (accept(Scanner.PLUS) || accept(Scanner.MINUS)){
       term();
       }
       }
       else
       printError(sym);        
       }
    */
    
    // term  =  factor { (* | / ) factor}
    /**DO NOT UNCOMMENT
       private void term() {
       if (sym==(Scanner.IDENT)||sym==(Scanner.NUMBER)||sym==Scanner.COLON||sym==Scanner.OPEN_PAREN){
       factor();
       while (accept(Scanner.MULT_OP) || accept(Scanner.DIV)){
       factor();
       }
       }
       else
       printError(sym);
       }
    */
    
    // factor  =  designator  |  number  | procedureCall |  _( expression _)
    /**DO NOT UNCOMMENT
       private void factor() {
       if (sym==(Scanner.IDENT)){
       designator();
       }
       else if (sym==(Scanner.NUMBER)){
       number();
       }
       else if (sym==(Scanner.COLON)){
       procedureCall();
       }
       else if (sym==(Scanner.OPEN_PAREN)){
       expect(Scanner.OPEN_PAREN);
       expression();
       expect(Scanner.CLOSE_PAREN);
       } else {
       printError(sym);
       }  
       }
    */
    
    // designator = ident { [ expr ]}
    /**DO NOT UNCOMMENT
       private void designator() {
       if (sym==Scanner.IDENT){
       ident();
            
       while (accept(Scanner.OPEN_BRKT)){
       expression();
       expect(Scanner.CLOSE_BRKT);
       }
       } else
       printError(sym);
       }
    */
    
    //whileStatement  =  _while condition _{ statementSequence  _}
    /**DO NOT UNCOMMENT
       private void whileStatement() {
       if (!expect(Scanner.WHILE)){
       return;
       }
       condition();
       expect(Scanner.OPEN_BRACE);
       statementSequence();
       expect(Scanner.CLOSE_BRACE);
       }
    */

    //condition  =  ( expression ( _== |  _!=  |  _< |  _<=  |  _>  |  _>= ) expression  )
    /**DO NOT UNCOMMENT
       private void condition() {
       expect(Scanner.OPEN_PAREN);
       expression();
       if ((!accept(Scanner.EQUAL))
       && (!accept(Scanner.NOT_EQ))
       && (!accept(Scanner.LESS_THAN))
       && (!accept(Scanner.LESS_THAN_EQ))
       && (!accept(Scanner.GRT_THAN))
       && (!accept(Scanner.GRT_THAN_EQ))){
       printError(sym);
       return;
       }
       expression();
       expect(Scanner.CLOSE_PAREN);
       }
    */
    
    
    /**
       ifStatement  =  _if condition _{ statementSequence  _}
       [  else_{ statementSequence  _} ]
       
       * */
    /**DO NOT UNCOMMENT
       private void ifStatement() {
       if (!expect(Scanner.IF)){
       return;
       }
       condition();
       expect(Scanner.OPEN_BRACE);
       statementSequence();
       expect(Scanner.CLOSE_BRACE);
       if (accept(Scanner.ELSE)){
       expect(Scanner.OPEN_BRACE);
       statementSequence();
       expect(Scanner.CLOSE_BRACE);
       }
       }
    */
    
    
    // output = _print _( parameters _) _;
    /**DO NOT UNCOMMENT
       private void output() {
       if (!expect(Scanner.PRINT)){
       return;
       }
       expect(Scanner.OPEN_PAREN);
       parameters();
       expect(Scanner.CLOSE_PAREN);
       expect(Scanner.SEMI_COLON);
       }
    */
    
    
    // input = _get _( parameters _) _;
    /**DO NOT UNCOMMENT
       private void input() {
       if (!expect(Scanner.GET)){
       return;
       }
       expect(Scanner.OPEN_PAREN);
       parameters();
       expect(Scanner.CLOSE_PAREN);
       expect(Scanner.SEMI_COLON);
       }
    */
    
    
    /**
       assignment  =  designator _= expression _;
       * */
    /**DO NOT UNCOMMENT
       private void assignment() {
       if (sym!=(Scanner.IDENT)){
       printError(sym);
       return;
       }
       designator();
       expect(Scanner.ASSIGN_OP);
       expression();
       expect(Scanner.SEMI_COLON);
       }
    */
    
    
    /**
       procedureDeclarations = {
       retType ident _( procedureFormalParams _) _{
       declarations
       statementSequence
       _}
       }
       
       * */
    private void proceduredeclarations(SymbolTable table) {
	// check for the empty case.
	if (sym==Scanner.IDENT || sym==Scanner.INT || sym==Scanner.SHORT || sym==Scanner.VOID){            
            while ((sym==Scanner.IDENT || sym==Scanner.INT || sym==Scanner.SHORT || sym==Scanner.VOID)){
		SymbolTable.TypeDesignator type = retType (table);
		SymbolTable.Symbol.SimplyTyped.Procedure procedure = new SymbolTable.Symbol.SimplyTyped.Procedure (type, table);
		bind (table, ident (), procedure);
		expect(Scanner.OPEN_PAREN);
		procedureFormalParams(procedure.table);
		expect(Scanner.CLOSE_PAREN);
		expect(Scanner.OPEN_BRACE);
		declarations(procedure.table);
                /**DO NOT UNCOMMENT
		   statementSequence();
                */
		expect(Scanner.CLOSE_BRACE);
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

    //    private SymbolTable
    
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
                    SymbolTable.Symbol symbol = new SymbolTable.Symbol.Constant ((short) number());
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
            int size = number ();
            expect (Scanner.OF);
            SymbolTable.TypeDesignator baseType = type (table);
	    return new SymbolTable.TypeDesignator.Array (baseType, size);
	} else
	    return type (table);
    }
        
    private int number() {
        if (expect(Scanner.NUMBER)){
        }
	return Scanner.val;
    }
    
    private String ident() {
        if (expect(Scanner.IDENT)){
        }
	return lexeme;
    }
    
    
    // parameters = designator { _, designator}
    /**DO NOT UNCOMMENT
       private void parameters()
       {
       if (sym!=Scanner.IDENT){
       printError(sym);
       return;
       }        
       designator();
       while(accept(Scanner.COMMA)){
       designator();
       }
       }
    */
        
    /**If you choose to use this design, you might want to look at Recursive_descent_parser in Wikipedia
     * Although you are welcome to use any other design you can think of. */
    private boolean accept(int s) {
        if (sym == s) {
            lexeme = Scanner.getLexeme();
            sym=Scanner.getSym();
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
 	final static String ID = "77672953";
 	final static String Name = "Max Nanasy";
 	final static String UCINetID = "mnanasy";
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
