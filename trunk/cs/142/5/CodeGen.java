import java.io.*;
import java.util.Vector;

/* NOTE: PLEASE FEEL FREE TO USE ALL, PART, OR NONE OF THIS FILE
   IT IS SIMPLY GIVEN TO SERVE AS A STARTING POINT */


public class CodeGen {

    public static String fp = "$fp";
    public static String sp = "$sp";
    public static String gp = "$gp";
    public static String zero = "$0";
    Boolean tempRegs[]; //there are 8 temporary registers
    Boolean args[];     //there are 4 arguments
    Boolean savedTempRegs[];//there are 8 saved temporary registers   
    Vector<String> codeSeg; //Storage for code/text segment
    Vector<String> dataSeg; //Storage for any data constants
	
    int nextInstruction; //Storage for next available instruction location
    int nextLocalLocation;//Storage for counting the next available local data cell
    int nextGlobalLocation;//Storage for counting the next available global data cell
    int labelCounter; //Used for generating unique labels as needed throughout the program
   
    CodeGen()
    {
        tempRegs = new Boolean[8];
        args = new Boolean[8];
        savedTempRegs = new Boolean[8];
        nextInstruction = 0;
        nextLocalLocation = 0;
        nextGlobalLocation = 0;
        codeSeg = new Vector<String>();
        dataSeg = new Vector<String>();
        labelCounter = 0;
      
        for(int i = 0; i < 8; i++)
            args[i] = savedTempRegs[i] = tempRegs[i] = false;    	  

    }

    //Returns a unique label
    public int makeLabel() { return labelCounter ++; }

    public void label (int label)
    {
        codeSeg.add ("L" + label + ":");
    }
    
    public void branch (int label)
    {
        codeSeg.add ("b L" + label);
    }

    public void branchIfEqual          (int label, int register0, int register1)
    {
        codeSeg.add ("beq $t" + register0 + ", $t" + register1 + ", L" + label);
    }

    public void branchIfNotEqual       (int label, int register0, int register1)
    {
        codeSeg.add ("bne $t" + register0 + ", $t" + register1 + ", L" + label);
    }
    
    public void branchIfGreaterOrEqual (int label, int register0, int register1)
    {
        codeSeg.add ("bge $t" + register0 + ", $t" + register1 + ", L" + label);
    }

    public void branchIfGreater        (int label, int register0, int register1)
    {
        codeSeg.add ("bgt $t" + register0 + ", $t" + register1 + ", L" + label);
    }

    public void branchIfLessOrEqual    (int label, int register0, int register1)
    {
        codeSeg.add ("ble $t" + register0 + ", $t" + register1 + ", L" + label);
    }

    public void branchIfLess           (int label, int register0, int register1)
    {
        codeSeg.add ("blt $t" + register0 + ", $t" + register1 + ", L" + label);
    }

    //Insert an allocation command into the data segment
    public void insertData(String data)
    {
        dataSeg.add(data);
    }
    
    //Resets the local allocation counter (i.e. when you exit a procedure)
    public void resetLocalLocation()
    {
        nextLocalLocation = 0;
    }
    
    //Resets the global allocation counter (if you should need it)
    public void resetGlobalLocation()
    {
        nextGlobalLocation = 0;
    }
    
    //Allocates memory by incrementing the local location counter
    //Returns the first address of the memory block allocated
    //Allocates a memory block as specified in allocationSize
    //Allocates based on the current local data segment counter
    public int getNextLocalLocation(int allocationSize)
    {
        int offset = nextLocalLocation;
        nextLocalLocation += allocationSize;
        return offset;
    }

    //Allocates memory by incrementing the global location counter
    //Returns the first address of the memory block allocated
    //Allocates a memory block as specified in allocationSize
    //Allocates based on the current global data segment counter
    public int getNextGlobalLocation(int allocationSize)
    {
        int offset = nextGlobalLocation;
        nextGlobalLocation += allocationSize;
        insertData (".word 0");
        return offset;
    }
    
    //Returns the text of the instruction at the position specified
    public String getInstructionAt(int position)
    {
        return codeSeg.elementAt(position);
    }
    
    //Substitutes the text of the instruction at the position specified
    //with the value stored in update string
    public void updateInstructionAt(int position, String update)
    {
        /* FILL THIS IN */
    }
    
    //Return the next available instruction location in the code segment
    private int getNextInstruction() {
        return codeSeg.size();
    }
    
    //Return the next available instruction location in the data segment
    public int getNextDataNumber() {
        return dataSeg.size();
    }

    public void loadConstant (int register, int value)
    {
        codeSeg.add ("add $t" + register + ", $0, " + value);
    }

    public void loadValue (int register, int offset)
    {
        codeSeg.add ("lw  $t" + register + ", " + offset + "($gp)");
    }

    public void storeValue (int register, int offset)
    {
        codeSeg.add ("sw  $t" + register + ", " + offset + "($gp)");
    }

    //allocate a temporary register
    public int getTemporaryRegister()
    { for(int i = 0; i < 8; i++)
            if(!tempRegs[i])
                {
                    tempRegs[i] = true;
                    return i;
                }
        return -1;
    }

    //allocate a temporary register that is saved across a call
    public int getTemporarySavedRegister()
    { for(int i = 0; i < 8; i++)
            if(!savedTempRegs[i])
                {  
                    savedTempRegs[i] = true;
                    return i;
                }
        return -1;
    }
    
    //release a temporary register indicated by regNum
    public void releaseTemporaryRegister(int regNum)
    {
        tempRegs[regNum] = false;
    }
	
    //release a saved temporary register indicated by regNum
    public void releaseTemporarySavedRegister(int regNum)
    {
        savedTempRegs[regNum] = false;
    }
	
    //deallocate all temporary registers
    public void releaseAllTemporaryRegisters()
    {
        for (int i = 0; i < 8; i++) releaseTemporaryRegister (i);
    }

    //deallocate all saved temporary registers
    public void releaseAllTemporarySavedRegisters()
    {
        for (int i = 0; i < 8; i++) releaseTemporarySavedRegister (i);
    }
	
    //indicate which instruction in the code segment is the first instruction in main
    //used to determine where/when to print out the label for main
    public void setMainInstruction()
    {
        codeSeg.add ("main:");
        codeSeg.add ("la $gp, base");
    }

    //generate code to print an integer; the value is stored in the register number
    //indicated by parameter reg
    public void printRegister(int reg)
    {
        codeSeg.add("move      $a0, $t"+reg+"       # load the integer");
        codeSeg.add("li      $v0,1                  # Prepare to print an integer");
        codeSeg.add("syscall                        # print it!!");
        codeSeg.add("la $a0, newline                # and then print out a newline.");
        codeSeg.add("li $v0, 4 ");
        codeSeg.add("syscall        ");
    }

    //generate code to read an integer; the value is stored into a register and the 
    //register number is the return result of the function
    public void inputToRegister(int register)
    {
        syscall (5);
        codeSeg.add ("move $t" + register + ", $v0");
    }

    public void add      (int registerS, int register0, int register1)
    {
        codeSeg.add ("add $t" + registerS + ", $t" + register0 + ", $t" + register1);
    }

    public void subtract (int registerS, int register0, int register1)
    {
        codeSeg.add ("sub $t" + registerS + ", $t" + register0 + ", $t" + register1);
    }

    public void multiply (int registerS, int register0, int register1)
    {
        codeSeg.add ("mul $t" + registerS + ", $t" + register0 + ", $t" + register1);
    }

    public void divide   (int registerS, int register0, int register1)
    {
        codeSeg.add ("div $t" + registerS + ", $t" + register0 + ", $t" + register1);
    }

    private void syscall (int callNumber)
    {
        codeSeg.add ("li $v0, " + callNumber);
        codeSeg.add ("syscall");
    }

    //generate code to exit the program
    public void exitProgram ()
    {
        syscall (10);
    }
	
    //Print the program to the provided stream
    public void dumpProgram(PrintStream s)
    {
        s.println(".data                         # BEGIN Data Segment");
        s.println("newline:      .asciiz       \"\\n\"");
        s.println("base:");
	
        for(String datum : dataSeg)
            s.println(datum);

        s.println("                              # END Data Segment");
		
		
        s.println(".text                         # BEGIN Code Segment");
        for(int i = 0; i < codeSeg.size(); i++)
            s.println(codeSeg.elementAt(i));
		    s.println("                              # END Code Segment");
    }
}
