package scanner;

import java.io.*;

public class Scanner
{

    // Definitions of the Token Values
    public static final int 
	ERROR =  0, GET =  1, PRINT   =  2, 

	IF    =  3, ELSE    =  4, WHILE = 5, 
	
	VAR = 6, CONST = 7, TYPE  = 8,  MAIN = 9,  

	INT = 10, VOID = 11, SHORT = 12, RETURN = 13, OF = 14,
	
	
	SEMI_COLON = 15, PERIOD = 16, AMPERSAND = 17, OPEN_PAREN = 18,

	CLOSE_PAREN = 19, OPEN_BRKT = 20, CLOSE_BRKT = 21, OPEN_BRACE = 22, 
	
	CLOSE_BRACE = 23, COLON = 24, COMMA = 25, ASSIGN_OP = 26, 
	
	PLUS = 27, MINUS = 28, MULT_OP = 29, DIV =  30, 

	
	EQUAL = 31, NOT_EQ = 32,GRT_THAN = 33, GRT_THAN_EQ = 34, LESS_THAN = 35, LESS_THAN_EQ = 36, 
	
	ARRAY = 37, END_OF = 38, IDENT = 39, NUMBER = 40;
  
    // textual representation of tokens
    public static final String Terminal[] = {
	"ERROR", "GET", "PRINT", "IF", "ELSE",

	"WHILE", "VAR", "CONST", "TYPE", "MAIN",

	"INT", "VOID", "SHORT", "RETURN","OF",
  
	";", ".", "&", "(", ")", "[", "]", "{", "}", ":", ",", "=", 
  
	"+", "-", "*", "/", 
											   
	"==", "!=", ">", ">=", "<", "<=", "ARRAY",
  
	"<EOT>", "ident", "number" };    

    private static final int EOF = -1;
    private static final int KEYWORDS_START  = GET       , KEYWORDS_END  = ARRAY     + 1;
    private static final int OPERATORS_START = SEMI_COLON, OPERATORS_END = LESS_THAN + 1;

    private int currentChar, nextChar;

    private LineNumberReader in;
    private PrintStream fileData;

    public Scanner(String sourceFile) throws IOException
    {
	in = new LineNumberReader (new FileReader (sourceFile));
	in.setLineNumber (1);
	readChar (); // inits scanner    
	fileData = new PrintStream (new FileOutputStream (sourceFile + ".out"));
    }
  
  
    public static void main( String args[])
    {
  
	try {
	
	    Scanner scanner = new Scanner(new String(args[0]));    

	    int token = -1;    

	    while( token != END_OF && token != ERROR ) {
		token = scanner.getSym ();
		scanner.fileData.print (" " + Terminal [token] + " ");
	    }

	}

	catch (IOException e) {
	    e.printStackTrace ();
	    System.err.println ("init: Errors accessing source file " + args [0]);
	    System.exit (-2);    
	}

    }

    private void readChar () throws IOException
    {
	currentChar = nextChar;
	nextChar = in.read ();
    }

    private static boolean isWhitespace (int c)
    {
	return c == ' ' || c == '\t' || c == '\n' || c == EOF;
    }

    private static boolean isLetter (int c)
    {
	return c >= 'A' && c <= 'Z' || c >= 'a' && c <= 'z';
    }

    private static boolean isDigit (int c)
    {
	return c >= '0' && c <= '9';
    }

    private static String toLowerCase (String s)
    {
	StringBuilder sb = new StringBuilder ();
	for (int i = 0; i < s.length (); i++)
	    sb.append (toLowerCase (s.charAt (i)));
	return sb.toString ();
    }

    private static char toLowerCase (char c)
    {
	return c >= 'A' && c <= 'Z' ? (char) (c + ('a' - 'A')) : c;
    }

    // Returns the current line number  
    public int getLineNumber()
    {
	return in.getLineNumber();  
    }

    private String getToken () throws IOException
    {
	if (isLetter (nextChar) || isDigit (nextChar)) {
	    readChar ();
	    return Character.toString ((char) currentChar) + getToken ();
	}
	return "";
    }

    private int tokenToIdentOrKeyword (String token)
    {
	for (int i = KEYWORDS_START; i < KEYWORDS_END; i++)
	    if (token.equals (toLowerCase (Terminal [i])))
		return i;
	return IDENT;
    }

    private int getIdentOrKeyword () throws IOException
    {
	return tokenToIdentOrKeyword (getToken ());
    }

    private int getNumber () throws IOException
    {
	if (isDigit (nextChar)) {
	    readChar ();
	    return getNumber ();
	}
	return NUMBER;
    }

    private int getOperator () throws IOException
    {
	switch (nextChar) {
	case '=':
	    readChar ();
	    if (nextChar == '=') {
		readChar ();
		return EQUAL;
	    }
	    else
		return ASSIGN_OP;
	case '!':
	    readChar ();
	    if (nextChar == '=') {
		readChar ();
		return NOT_EQ;
	    }
	    else
		return ERROR;
	case '>':
	    readChar ();
	    if (nextChar == '=') {
		readChar ();
		return GRT_THAN_EQ;
	    }
	    else
		return GRT_THAN;
	case '<':
	    readChar ();
	    if (nextChar == '=') {
		readChar ();
		return LESS_THAN_EQ;
	    }
	    else 
		return LESS_THAN;
	default:
	    for (int i = OPERATORS_START; i < OPERATORS_END; i++)
		if (nextChar == Terminal [i].charAt (0)) {
		    readChar ();
		    return i;
		}
	    return ERROR;
	}
    }

    public int getSym () throws IOException
    {

	if (nextChar == EOF)
	    return END_OF;
	if (isWhitespace (nextChar)) {
	    readChar ();
	    return getSym ();
	}

	if (isLetter (nextChar)) return getIdentOrKeyword ();
	if (isDigit (nextChar)) return getNumber ();

	return getOperator ();

    }

}  
