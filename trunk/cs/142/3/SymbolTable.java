import java.util.*;
import java.io.*;

public class SymbolTable extends LinkedList <SymbolTable.Entry <String, SymbolTable.Symbol>>
{

    SymbolTable parent;

    SymbolTable (SymbolTable p)
	{
	    parent = p;
	}

    SymbolTable ()
	{
	    parent = null;
	}

    public Symbol getBinding (String name, String clase)
    {
	//	System.out.println ("START " + name + " " + clase);
	for (SymbolTable table = this; table != null; table = table.parent)
	    for (Entry <String, Symbol> entry : table) {
		//		System.out.println ("start " + entry.key + " " + entry.value.clase ());
		if (entry.key.equals (name) && entry.value.clase ().equals (clase)) {
		    //		    System.out.println ("end " + entry.key + " " + entry.value.clase ());
		    //		    System.out.println ("END " + name + " " + clase);
		    return entry.value;
		}
	    }
	return null;
    }

    public boolean bind (String name, Symbol symbol)
    {
	for (Entry <String, Symbol> entry : this)
	    if (entry.key.equals (name) && conflict (symbol, entry.value))
		return false;
	add (new Entry <String,Symbol> (name, symbol));
	return true;
    }

    public void printSymTable (PrintStream output)
    {
	output.println ("***** Symbol Table Contents *****");
	printTo (output, 0);
    }

    private void printTo (PrintStream output, int indentationLevel)
    {
	for (Entry <String, Symbol> entry : this) {
	    for (int i = 1; i < indentationLevel; i++)
		output.print ("---");
	    if (indentationLevel != 0)
		output.print ("-->");
	    output.print ("N: " + entry.key + " ");
	    printSymbolTo (entry.value, output, indentationLevel);
	}
    }

    public static class Entry <K, V>
    {
	public K key;
	public V value;
	Entry () { };
	Entry (K k, V v)
	    {
		key = k;
		value = v;
	    }
    }

    private void printSymbolTo (Symbol symbol, PrintStream output, int il)
    {
	output.print ("C: " + symbol.clase () + " T: " + symbol.type () + " ");
	symbol.printValueTo (output, il);
    }

    private static boolean conflict (Symbol symbol0, Symbol symbol1)
    {
	String clase0 = symbol0.clase ()
	     , clase1 = symbol1.clase ();
	return clase0.equals (clase1) || clase0.equals ("VAR") && clase1.equals ("CONST") || clase0.equals ("CONST") && clase1.equals ("VAR");
    }

    public interface TypeDesignator
    {

	public class Atomic implements TypeDesignator
	{
	    String name;
	    Atomic (String n)
	    {
		name = n;
	    }
	    public String toString () { return name; }
	}

	public class Array implements TypeDesignator
	{
	    TypeDesignator baseType;
	    int length;
	    Array (TypeDesignator bt, int l)
	    {
		length = l;
		baseType = bt;
	    }
	    public String toString () { return baseType + " D: " + length; }
	}

	public static final TypeDesignator
	      SHORT = new Atomic ("short")
	    , INT   = new Atomic ("int"  )
	    , VOID  = new Atomic ("void" )
	    , NULL  = new Atomic ("null" )
	    ;

    }

    public interface Symbol
    {

	public String clase ();
	public TypeDesignator type  ();
	public void printValueTo (PrintStream output, int indentationLevel);

	public class Constant implements Symbol
	{

	    short value;

	    Constant (short v)
	    {
		value = v;
	    }

	    public String clase () { return "CONST"; }
	    public TypeDesignator type  () { return TypeDesignator.SHORT; }

	    public void printValueTo (PrintStream output, int il)
	    {
		output.println ("V: " + value);
	    }

	}

	abstract class SimplyTyped implements Symbol
	{

	    TypeDesignator type;
	    SimplyTyped (TypeDesignator t)
	    {
		type = t;
	    }

	    public TypeDesignator type () { return type; }

	    public static class Procedure extends SimplyTyped
	    {

		public SymbolTable table;

		Procedure (TypeDesignator t, SymbolTable parent)
		{
		    super (t);
		    table = new SymbolTable (parent);
		}

		public String clase () { return "PROCEDURE"; }
		public void printValueTo (PrintStream output, int il)
		{
		    output.println ();
		    if (table != null) table.printTo (output, il + 1);
		}

	    }

	    public static class Variable extends SimplyTyped
	    {
		public String clase () { return "VAR"; }
		public void printValueTo (PrintStream output, int il) { output.println (); }

		Variable (TypeDesignator t)
		{
		    super (t);
		}

	    }

	    public static class Type extends SimplyTyped
	    {

		public String clase () { return "TYPE"; }
		public void printValueTo (PrintStream output, int il) { output.println (); }

		Type (TypeDesignator t)
		{
		    super (t);
		}

		public static final Type
		      SHORT = new Type (TypeDesignator.SHORT )
		    , INT   = new Type (TypeDesignator.SHORT )
		    , VOID  = new Type (TypeDesignator.SHORT )
		    ;

	    }

	}

    }

}
