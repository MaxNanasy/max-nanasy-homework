import java.io.*;
import java.util.*;

public class Parser
{
    public static int NO_ERROR=-1, SYNTAX_ERROR = 0, SEMANTIC_ERROR = 1,
        UNDEFINED_ERROR = 2, REDEFINED_ERROR = 3, MISMATCH_ERROR=4, ARITY_ERROR=5;

    private Scanner scanner;
    public int sym; //Stores the current input from getSym()
    String lexeme;

    private int returnLabel;

    private SymbolTable symbolTable;
    private CodeGen codeGen;
    
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

    public SymbolTable.Symbol getVarOrConstBinding (SymbolTable table, String name)
    {
        SymbolTable.Symbol symbol = table.getBinding (name, "VAR");
        if (symbol == null) {
            symbol = table.getBinding (name, "CONST");
            if (symbol == null)
                printError (SEMANTIC_ERROR, UNDEFINED_ERROR);
        }
        return symbol;
    }
    
    private void printError(int errorType, int symOrError)
    {
        //For Comparing Output: please use this format as it will be used
        //to compare output results
        System.err.println("Error: " + ((errorType == SYNTAX_ERROR)? "SYNTAX: "
                                        : "SEMANTIC: ") +
                           ((errorType == SYNTAX_ERROR)? Scanner.Terminal[symOrError] :
                            (symOrError == UNDEFINED_ERROR)? " UNDEFINED SYMBOL" :
                            (symOrError == REDEFINED_ERROR) ? "REDEFINED SYMBOL" :
                            (symOrError == MISMATCH_ERROR) ? "TYPE MISMATCH" : "ARITY ERROR"));
        
        symbolTable.printSymTable(System.err);
        
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
        codeGen = new CodeGen ();

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
        returnLabel = codeGen.makeLabel ();
        codeGen.label (returnLabel);
        //        codeGen.popTemporaryRegisters ();
        codeGen.ret ();
        declarations(table);
        proceduredeclarations(table);
        expect(Scanner.MAIN);
        codeGen.setMainInstruction ();
        expect(Scanner.OPEN_PAREN);
        expect(Scanner.CLOSE_PAREN);
        expect(Scanner.OPEN_BRACE);
        SymbolTable.Symbol.SimplyTyped.Procedure main = new SymbolTable.Symbol.SimplyTyped.Procedure (SymbolTable.TypeDesignator.VOID, table, codeGen.makeLabel ());
        bind (table, "MAIN", main);
        declarations (main.table);
        statementSequence (main.table, SymbolTable.TypeDesignator.VOID);
        codeGen.exitProgram ();
        expect(Scanner.CLOSE_BRACE);
        expect(Scanner.END_OF);
        main.parameters = null;
        main.table = null;
    }
    
    /**
       statementSequence  =  statement {statement}
       * */
    private void statementSequence(SymbolTable table, SymbolTable.TypeDesignator enclosingType)
    {
        if (! statement (table, enclosingType)) {
            printError(sym);
            return;
        }
        while (statement (table, enclosingType));
    }

    /**
       statement =  assignment | input | output | ifStatement | whileStatement | returnStatement | procedureStatement.
       * */
    private boolean statement (SymbolTable table, SymbolTable.TypeDesignator enclosingType) {
        switch (sym) {
        case Scanner.IDENT : assignment         (table); break;
        case Scanner.GET   : input              (table); break;
        case Scanner.PRINT : output             (table); break;
        case Scanner.IF    : ifStatement        (table, enclosingType); break;
        case Scanner.WHILE : whileStatement     (table, enclosingType); break;
        case Scanner.COLON : procedureStatement (table); break;
        case Scanner.RETURN: returnStatement    (table, enclosingType); break;
        default: return false;
        }
        return true;
    }

    // procedureStatement = procedureCall ;
    private void procedureStatement (SymbolTable table) {
        procedureCall (table).evaluateStandalone (codeGen, table);
        expect(Scanner.SEMI_COLON);
    }
    
    // procedureCall = :: ident  ( [parameters] )
    private Expression procedureCall (SymbolTable table) {
        expect (Scanner.COLON);
        expect (Scanner.COLON);
        String name = ident ();
        SymbolTable.Symbol.SimplyTyped.Procedure procedure = (SymbolTable.Symbol.SimplyTyped.Procedure) getBinding (table, name, "PROCEDURE");
        expect (Scanner.OPEN_PAREN);
        if (! accept (Scanner.CLOSE_PAREN)) {
            List <Expression.Designator> arguments = parameters (table);
            Iterator <Expression.Designator> ai;
            Iterator <SymbolTable.Entry <String, SymbolTable.Symbol>> pi;
            for (ai = arguments.iterator (), pi = procedure.parameters.iterator (); ai.hasNext () && pi.hasNext ();) {
                Expression.Designator a = ai.next ()      ;
                SymbolTable.Symbol    p = pi.next ().value;
                if (((SymbolTable.Symbol.SimplyTyped.Variable) p).reference)
                    if (! a.referenceable (table)) printError (SEMANTIC_ERROR, MISMATCH_ERROR);
                if (SymbolTable.TypeDesignator.Combine.procedureArgument (p.type (), a.type (table)) == null) printError (SEMANTIC_ERROR, MISMATCH_ERROR);
            }
            if (ai.hasNext () || pi.hasNext ())
                printError (SEMANTIC_ERROR, ARITY_ERROR);
	    
	    
            expect(Scanner.CLOSE_PAREN);
            return new Expression.ProcedureCall (name, arguments);
        }
        else if (procedure.parameters.isEmpty ()) return new Expression.ProcedureCall (name, new LinkedList <Expression.Designator> ());
        else printError (SEMANTIC_ERROR, ARITY_ERROR);
        return null;
    }

    // returnStatement = _return  expression _;
    private void returnStatement (SymbolTable table, SymbolTable.TypeDesignator enclosingType) {
        expect (Scanner.RETURN);
        Expression returnValue = expression (table);
        int returnValueRegister = codeGen.getTemporaryRegister ();
        returnValue.evaluateIntoRegister (codeGen, returnValueRegister, table);
        codeGen.storeReturnValue (returnValueRegister);
        codeGen.releaseTemporaryRegister (returnValueRegister);
        exitProcedure ();
        if (SymbolTable.TypeDesignator.Combine.procedureReturn (enclosingType, returnValue.type (table)) == null)
            printError (SEMANTIC_ERROR, MISMATCH_ERROR);
        expect (Scanner.SEMI_COLON);
    }
 
    // expression  =  term { ( + | - ) term }
    private Expression expression (SymbolTable table)
    {
        if (sym==(Scanner.IDENT)||sym==(Scanner.NUMBER)||sym==Scanner.COLON||sym==Scanner.OPEN_PAREN){
            Expression expression = term (table);
            for (;;) {
                if      (accept (Scanner.PLUS )) expression = new Expression.BinaryOperation.Addition    (expression, term (table));
                else if (accept (Scanner.MINUS)) expression = new Expression.BinaryOperation.Subtraction (expression, term (table));
                else break;
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
            for (;;) {
                if      (accept (Scanner.MULT_OP)) expression = new Expression.BinaryOperation.Multiplication (expression, factor (table));
                else if (accept (Scanner.DIV    )) expression = new Expression.BinaryOperation.Division       (expression, factor (table));
                else break;
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
        case Scanner.IDENT : return designator    (table)            ;
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
    private Expression.Designator designator (SymbolTable table)
    {
        if (sym==Scanner.IDENT){
            String name = ident ();
            getVarOrConstBinding (table, name);
            Expression.Designator designator = new Expression.Designator.Variable (name);
            while (accept (Scanner.OPEN_BRKT)) {
                designator = new Expression.Designator.ArrayReference (designator, expression (table));
                expect(Scanner.CLOSE_BRKT);
            }
            SymbolTable.TypeDesignator type = designator.type (table);
            if (type == null || type.dereferencedType () != null) printError (SEMANTIC_ERROR, ARITY_ERROR);
            return designator;
        } else {
            printError(sym);
            return null;
        }
    }
    
    //whileStatement  =  _while condition _{ statementSequence  _}
    private void whileStatement (SymbolTable table, SymbolTable.TypeDesignator enclosingType) {
        codeGen.comment ("BEGIN while statement");
        expect (Scanner.WHILE);
        int startLabel = codeGen.makeLabel (), endLabel = codeGen.makeLabel ();
        codeGen.label (startLabel);
        
        condition (endLabel, table);
        expect(Scanner.OPEN_BRACE);
        statementSequence (table, enclosingType);
        expect(Scanner.CLOSE_BRACE);
        codeGen.branch (startLabel);
        codeGen.label (endLabel);
        codeGen.comment ("END   While statement");
    }

    //condition  =  ( expression ( _== |  _!=  |  _< |  _<=  |  _>  |  _>= ) expression  )
    private void condition (int label, SymbolTable table) {
        expect(Scanner.OPEN_PAREN);
        int register0 = codeGen.getTemporaryRegister ();
        expression (table).evaluateIntoRegister (codeGen, register0, table);
        int condition = Scanner.END_OF;
        for (int c : new Integer [] { Scanner.EQUAL, Scanner.NOT_EQ, Scanner.LESS_THAN, Scanner.LESS_THAN_EQ, Scanner.GRT_THAN, Scanner.GRT_THAN_EQ })
            if (accept (c))
                condition = c;
        if (condition == Scanner.END_OF) printError (sym);
        int register1 = codeGen.getTemporaryRegister ();
        expression (table).evaluateIntoRegister (codeGen, register1, table);
        codeGen.releaseTemporaryRegister (register0);
        codeGen.releaseTemporaryRegister (register1);
        switch (condition) {
        case Scanner.EQUAL       : codeGen.branchIfNotEqual       (label, register0, register1); break;
        case Scanner.NOT_EQ      : codeGen.branchIfEqual          (label, register0, register1); break;
        case Scanner.LESS_THAN   : codeGen.branchIfGreaterOrEqual (label, register0, register1); break;
        case Scanner.LESS_THAN_EQ: codeGen.branchIfGreater        (label, register0, register1); break;
        case Scanner.GRT_THAN    : codeGen.branchIfLessOrEqual    (label, register0, register1); break;
        case Scanner.GRT_THAN_EQ : codeGen.branchIfLess           (label, register0, register1); break;
        default:
        }
        expect(Scanner.CLOSE_PAREN);
    }
    
    /* ifStatement  =  _if condition _{ statementSequence  _}
       [  else_{ statementSequence  _} ] */

    private void ifStatement (SymbolTable table, SymbolTable.TypeDesignator enclosingType) {
        codeGen.comment ("BEGIN if statement");
        int endLabel = codeGen.makeLabel (), elseLabel = codeGen.makeLabel ();
        expect(Scanner.IF);
        condition (elseLabel, table);
        expect (Scanner.OPEN_BRACE);
        statementSequence (table, enclosingType);
        codeGen.branch (endLabel);
        expect (Scanner.CLOSE_BRACE);
        codeGen.label (elseLabel);
        if (accept (Scanner.ELSE)){
            expect (Scanner.OPEN_BRACE);
            statementSequence (table, enclosingType);
            expect (Scanner.CLOSE_BRACE);
        }
        codeGen.label (endLabel);
        codeGen.comment ("END   if statement");
    }
    
    // output = _print _( parameters _) _;
    private void output (SymbolTable table)
    {
        expect(Scanner.PRINT);
        expect(Scanner.OPEN_PAREN);
        int register = codeGen.getTemporaryRegister ();
        for (Expression e : parameters (table)) {
            e.evaluateIntoRegister (codeGen, register, table);
            codeGen.printRegister (register);
        }
        codeGen.releaseTemporaryRegister (register);
        expect(Scanner.CLOSE_PAREN);
        expect(Scanner.SEMI_COLON);
    }
    
    // input = _get _( parameters _) _;
    private void input (SymbolTable table)
    {
        expect(Scanner.GET);
        expect(Scanner.OPEN_PAREN);
        int register = codeGen.getTemporaryRegister ();
        for (Expression.Designator d : parameters (table)) {
            if (! d.referenceable (table)) printError (SEMANTIC_ERROR, MISMATCH_ERROR);
            codeGen.inputToRegister (register);
            d.assignRegisterTo (codeGen, register, table);
        }
        codeGen.releaseTemporaryRegister (register);
        expect(Scanner.CLOSE_PAREN);
        expect(Scanner.SEMI_COLON);
    }
    
    /**
       assignment  =  designator _= expression _;
       * */
    private void assignment (SymbolTable table)
    {
        if (sym != Scanner.IDENT) printError(sym);
        Expression.Designator designator = designator (table);
        SymbolTable.TypeDesignator type0 = designator.type (table);
        if (type0.dereferencedType () != null) printError (SEMANTIC_ERROR, ARITY_ERROR);
        expect(Scanner.ASSIGN_OP);
        Expression expression = expression (table);
        SymbolTable.TypeDesignator type1 = expression.type (table);
        if (SymbolTable.TypeDesignator.Combine.assignment (type0, type1) == null) printError (SEMANTIC_ERROR, MISMATCH_ERROR);
        int register = codeGen.getTemporaryRegister ();
        expression.evaluateIntoRegister (codeGen, register, table);
        designator.assignRegisterTo (codeGen, register, table);
        codeGen.releaseTemporaryRegister (register);
        expect(Scanner.SEMI_COLON);
    }
    
    
    /**
       procedureDeclarations = {
       retType ident _( procedureFormalParams _) _{
       declarations
       statementSequence
       _}
       } **/

    private void exitProcedure ()
    {
        codeGen.branch (returnLabel);
    }

    private void proceduredeclarations(SymbolTable table) {
        // check for the empty case.
        if (sym==Scanner.IDENT || sym==Scanner.INT || sym==Scanner.SHORT || sym==Scanner.VOID){            
            while ((sym==Scanner.IDENT || sym==Scanner.INT || sym==Scanner.SHORT || sym==Scanner.VOID)){
                codeGen.comment ("BEGIN procedure");
                SymbolTable.TypeDesignator type = retType (table);
                SymbolTable.Symbol.SimplyTyped.Procedure procedure = new SymbolTable.Symbol.SimplyTyped.Procedure (type, table, codeGen.makeLabel ());
                bind (table, ident (), procedure);
                codeGen.label (procedure.label);
                //                codeGen.pushTemporaryRegisters ();
                expect (Scanner.OPEN_PAREN);
                procedureFormalParams (procedure.parameters, procedure.table);
                expect (Scanner.CLOSE_PAREN);
                expect (Scanner.OPEN_BRACE);
                declarations (procedure.table);
                statementSequence (procedure.table, type);
                expect (Scanner.CLOSE_BRACE);
                exitProcedure ();
                codeGen.comment ("END   procedure");
            }
        }
    }
    
    // procedureFormalParams = [ type [ _& ] ident {_, type [ _& ] ident }]
    private void procedureFormalParams(SymbolTable parameters, SymbolTable table) {
        codeGen.resetLocalLocation ();
        if (nextIsType ()){
            do {
                SymbolTable.TypeDesignator type = type (table);
                boolean reference = accept(Scanner.AMPERSAND);
                String name = ident();
                SymbolTable.Symbol.SimplyTyped.Variable variable = new SymbolTable.Symbol.SimplyTyped.Variable (type, codeGen.getNextLocalLocation (type.dataSize ()), reference, true);
                bind (parameters, name, variable);
                bind (table     , name, variable);
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
            return new SymbolTable.TypeDesignator.Named (name, getBinding (table, name, "TYPE").type ());
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
                    for (String name : names) bind (table, name, new SymbolTable.Symbol.SimplyTyped.Variable (type, codeGen.getNextGlobalLocation (type.dataSize ()), false, false));
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
    private List <Expression.Designator> parameters (SymbolTable table)
    {
        if (sym != Scanner.IDENT) {
            printError (sym);
            return null;
        }
        LinkedList <Expression.Designator> parameters = new LinkedList <Expression.Designator> ();
        do {
            parameters.add (designator (table));
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

        PrintStream fileData = null;

        try {
            FileOutputStream outFile = new FileOutputStream(args[0]+".asm");
            fileData = new PrintStream( outFile );
        }
        
        catch (IOException e) {
            e.printStackTrace();
            System.err.println("init: Errors accessing output file: "+args[0]+".asm");
            System.exit(-2);
        }
        
        Parser p = new Parser(args);

        p.bind (p.symbolTable, "int"  , new SymbolTable.Symbol.SimplyTyped.Type (SymbolTable.TypeDesignator.NULL));
        p.bind (p.symbolTable, "void" , new SymbolTable.Symbol.SimplyTyped.Type (SymbolTable.TypeDesignator.NULL));
        p.bind (p.symbolTable, "short", new SymbolTable.Symbol.SimplyTyped.Type (SymbolTable.TypeDesignator.NULL));
        
        p.program (p.symbolTable);

        p.codeGen.dumpProgram (fileData);

    }
    
}
