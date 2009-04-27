package parser;

import java.io.*;

import static ebnf.EBNF.program;
import scanner.*;

public class Parser
{

    private Scanner scanner;
    private int sym; //Stores the current input from getSym()
    public int tabCount;
    private String oldOutput, output, errorOutput;

    public void printRule (String ruleName)
    {
	output = oldOutput;
	for(int i=0; i < tabCount; i++)
	    output += "   ";  //using 3 space indentation
	output += ruleName;
    }

    public void undoPrintRule ()
    {
	output = oldOutput;
    }

    public void printError(int symReceived)
    {
	//For Comparing Output: please use this format as it will be used
	//to compare output results
	errorOutput = "Error: " + Scanner.Terminal [symReceived];

	System.err.println(" Error Encountered on Line Number: " + scanner.getLineNumber());
	System.exit(-1);
    }

    public Parser(Scanner scanner) throws IOException
    {

	this.scanner = scanner;
	oldOutput = output = errorOutput = "";
	tabCount = 0;

	sym = scanner.getSym();

    }

    private boolean accept(int s) throws IOException {
	if (sym == s) {
	    sym = scanner.getSym();
	    return true;
	}
	return false;
    }

    public boolean expect(int s) throws IOException
    {
	if (accept(s))
	    return true;
	printError(sym);
	return false;
    }

    private class StudentInfo
    {
	final static String ID       = "77672953"  ;
	final static String Name     = "Max Nanasy";
	final static String UCINetID = "mnanasy"   ;
    }

    public static void main(String[] args) throws IOException
    {

	System.out.println (StudentInfo.ID      );
	System.out.println (StudentInfo.Name    );
	System.out.println (StudentInfo.UCINetID);

	Parser p = new Parser(new Scanner (args [0]));
	System.out.println (program.parse (p));
	new PrintStream (args [0] + ".out").println (p.output + p.errorOutput);
	

    }

}
