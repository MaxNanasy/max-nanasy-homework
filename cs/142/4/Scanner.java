
import java.io.*;

public class Scanner{  


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


	static int val; // value of last-scanned integer 
	static int sym; // last-scanned symbol for easy access
	static String ident;  // content of last-scanned identifier
	static String lexeme;
	private static int nextChar;  // contains the character (or -1==EOF)
	// which needs to be scanned next  
	private static LineNumberReader in;

	public static FileOutputStream outFile;

	private static PrintStream fileData;

	public Scanner(String sourceFile)
	{
		try {
			Scanner.in = new LineNumberReader(new FileReader(sourceFile));
			Scanner.in.setLineNumber(1);
			nextChar = Scanner.in.read(); // inits scanner    
			outFile = new FileOutputStream(sourceFile+".out");
			fileData = new PrintStream( outFile );
		}

		catch (IOException e) {        
			e.printStackTrace();
			System.err.println("init: Errors accessing source file " +sourceFile );
			System.exit(-2);    
		}             

	}


	public static void main( String args[]){        

		Scanner scanner = new Scanner(new String(args[0]));    




		int token = -1;    

		while( token != END_OF && token != ERROR ){
			token = getSym();
			fileData.print(" " + Terminal[ token ] + " ");
		}      
	}


	// Returns the current line number  
	public static int getLineNumber() {
		return Scanner.in.getLineNumber();  
	}

	public static int getSym() {

		try {			
			while ((nextChar != -1) && (nextChar <= ' ')) {				
				nextChar = Scanner.in.read();  			}  			
			if (nextChar == -1 || sym == PERIOD){				
				sym = END_OF;    				
				return END_OF;  			}  			
			else if (nextChar == '.') {				
				nextChar = Scanner.in.read();				
				sym = PERIOD;  			}			
			else if (nextChar == ':') {				
				nextChar = Scanner.in.read();     				
				sym = COLON;  			}  			
			else if (nextChar == '>') {				
				nextChar = Scanner.in.read();     				
				if (nextChar == '=') {					
					nextChar = Scanner.in.read();      					
					sym = GRT_THAN_EQ;    	}    				
				else					
					sym = GRT_THAN;  			
			}  			
			else if (nextChar == '!') {				
				nextChar = Scanner.in.read();     				
				if (nextChar == '=') {					
					nextChar = Scanner.in.read();      					
					sym = NOT_EQ;    				}    				
				else					sym = ERROR;  			
			}  			
			else if (nextChar == '<') {				
				nextChar = Scanner.in.read(); 				
				if (nextChar == '=') {					
					nextChar = Scanner.in.read();      					
					sym = LESS_THAN_EQ;				}				
				else if (nextChar == '>') {					
					nextChar = Scanner.in.read();						
					sym = NOT_EQ;				}				
				else					
					sym = LESS_THAN;  			}  			
			else if (nextChar == '+') {				
				nextChar = Scanner.in.read(); 				
				sym = PLUS;  			}			
			else if (nextChar == '-') {				
				nextChar = Scanner.in.read(); 				
				sym = MINUS;  			} 			
			else if (nextChar == '*') {				
				nextChar = Scanner.in.read(); 				
				sym = MULT_OP;  			} 			
			else if (nextChar == '/') {				
				nextChar = Scanner.in.read(); 				
				sym = DIV;  			} 			
			else if (nextChar == '=') {    				
				nextChar = Scanner.in.read(); 				
				if (nextChar == '=') {					
					nextChar = Scanner.in.read();      					
					sym = EQUAL;    				}    				
				else {					
					sym = ASSIGN_OP;				}			
			}  			
			else if (nextChar == ';') {    				
				nextChar = Scanner.in.read(); 				
				sym = SEMI_COLON;			}  			
			else if (nextChar == '&') {    				
				nextChar = Scanner.in.read(); 				
				sym = AMPERSAND;			}  			
			else if (nextChar == '(') {    				
				nextChar = Scanner.in.read(); 				
				sym = OPEN_PAREN;			}  			
			else if (nextChar == ')') {    				
				nextChar = Scanner.in.read(); 				
				sym = CLOSE_PAREN;			}  			
			else if (nextChar == '[') {    				
				nextChar = Scanner.in.read(); 				
				sym = OPEN_BRKT;			}  			
			else if (nextChar == ']') {    				
				nextChar = Scanner.in.read(); 				
				sym = CLOSE_BRKT;			}  			
			else if (nextChar == '{') {    				
				nextChar = Scanner.in.read(); 				
				sym = OPEN_BRACE;			}  			
			else if (nextChar == '}') {    				
				nextChar = Scanner.in.read(); 				
				sym = CLOSE_BRACE;			}  			
			else if (nextChar == ',') {    				
				nextChar = Scanner.in.read(); 				
				sym = COMMA;			}  			
			else if (((nextChar >= 'a') && (nextChar <= 'z'))					 
					|| ((nextChar >= 'A') && (nextChar <= 'Z'))){				
				// Scans identifiers    				
				StringBuffer buf = new StringBuffer("");				
				do {     buf.append((char)nextChar);					
				nextChar = Scanner.in.read();				
				} while ((nextChar >= 'a') && (nextChar <= 'z')
						|| (nextChar >= 'A') && (nextChar <= 'Z')						 
						|| (nextChar >= '0') && (nextChar <= '9'));    				
				ident = buf.toString();							
				for (int s = 1; s < Terminal.length; s++)//Start comparing at terminal 1, to ensure that 
					//ERROR (or any derivative) isn't detected as a token 
					if (ident.compareTo(Terminal[s].toLowerCase()) == 0){						
						sym = ((s == 39) ? 38 : s);						
						break;					
					} 					
					else
					{
						sym = IDENT;
						lexeme = new String(ident);
					}
			}  			
			else if( (nextChar >='0') && (nextChar <= '9') )				
			{ //Scans numbers					
				StringBuffer buf = new StringBuffer("");					
				val = 0;
				do {						buf.append((char)nextChar);						   
				    val = val * 10 + (nextChar - '0');
				nextChar = Scanner.in.read();					
				}while((nextChar >='0') && (nextChar <= '9'));								
				sym = NUMBER;					
				lexeme = new String(buf);
			}			
			else 				
			{					
				System.out.println("getSym: encountered unknown character "	
						+ (char)nextChar + "." 									   
						+ Scanner.in.getLineNumber());    					
				System.exit(1);				
			}		
		} catch (IOException e) {			
			System.out.println("getSym: read error." +							   
					Scanner.in.getLineNumber());			
			System.exit(-3);  		}			

		return sym;
	}  
	
	public static String getLexeme()
	{
		if(sym < Scanner.END_OF)
			return Terminal[sym];
		else
			return lexeme;
	}
}  
