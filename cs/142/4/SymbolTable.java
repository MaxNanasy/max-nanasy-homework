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
	for (SymbolTable table = this; table != null; table = table.parent)
	    for (Entry <String, Symbol> entry : table)
		if (entry.key.equals (name) && entry.value.clase ().equals (clase))
		    return entry.value;
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

    public static interface TypeDesignator
    {

	public TypeDesignator dereferencedType ();
	public TypeDesignator normalizedType ();

	public static final class Combine
	{

	    private static TypeDesignator symmetricallyNormalized (TypeDesignator type0, TypeDesignator type1)
	    {

		if (type0 == null || type1 == null) return null;

		String typeName0 = type0.toString ()
		     , typeName1 = type1.toString ();

		if (typeName0.equals ("void") || typeName1.equals ("void")) return null;
		if (typeName0.equals (typeName1)) return type0;
		if (typeName0.equals ("short") && typeName1.equals ("int"  )
	         || typeName0.equals ("int"  ) && typeName1.equals ("short")) return SymbolTable.TypeDesignator.INT;

		return null;

	    }
		

	    public static TypeDesignator symmetrically (TypeDesignator type0, TypeDesignator type1)
	    {
		return symmetricallyNormalized (type0 == null ? null : type0.normalizedType (), type1 == null ? null : type1.normalizedType ());
	    }

	    public static TypeDesignator assignment (TypeDesignator designatorType, TypeDesignator expressionType)
	    {
		if (designatorType != null) designatorType = designatorType.normalizedType ();
		if (expressionType != null) expressionType = expressionType.normalizedType ();
		if (designatorType != null && expressionType != null && designatorType.toString ().equals ("short") && expressionType.toString ().equals ("int")) return null;
		else return symmetricallyNormalized (designatorType, expressionType);
	    }

	    public static TypeDesignator procedureReturn (TypeDesignator procedureType, TypeDesignator returnType)
	    {
		return assignment (procedureType, returnType);
	    }

	    public static TypeDesignator procedureArgument (TypeDesignator parameterType, TypeDesignator argumentType)
	    {
		return assignment (parameterType, argumentType);
	    }

	}

	public class Named implements TypeDesignator
	{
	    String name;
	    TypeDesignator baseType;
	    Named (String n, TypeDesignator bt)
	    {
		name = n;
		baseType = bt;
	    }
	    public String toString () { return name; }
	    public TypeDesignator dereferencedType () { return baseType.dereferencedType (); }
	    public TypeDesignator normalizedType () { return baseType.normalizedType (); }
	}

	public class Atomic implements TypeDesignator
	{
	    String name;
	    Atomic (String n)
	    {
		name = n;
	    }
	    public String toString () { return name; }
	    public TypeDesignator dereferencedType () { return null; }
	    public TypeDesignator normalizedType () { return this; }
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
	    public TypeDesignator dereferencedType () { return baseType; }
	    public TypeDesignator normalizedType () { return new Array (baseType.normalizedType (), length); }
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

		public SymbolTable parameters, table;

		Procedure (TypeDesignator t, SymbolTable parent)
		{
		    super (t);
		    parameters = new SymbolTable ();
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
		boolean reference;

		Variable (TypeDesignator t, boolean r)
		{
		    super (t);
		    reference = r;
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
