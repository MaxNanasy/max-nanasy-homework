import java.util.*;

public interface Expression
{

    public SymbolTable.TypeDesignator type (SymbolTable table);

    interface Designator extends Expression
    {

	public class Variable implements Designator
	{

	    String name;

	    Variable (String n)
	    {
		name = n;
	    }

	    public SymbolTable.TypeDesignator type (SymbolTable table)
	    {
		SymbolTable.Symbol  symbol = table.getBinding (name, "VAR");
		if (symbol == null) symbol = table.getBinding (name, "CONST");
		if (symbol == null) return null;
		else                return symbol.type ();
	    }

	}

	public class ArrayReference implements Designator
	{

	    Designator baseDesignator;
	    Expression index;

	    ArrayReference (Designator bd, Expression i)
	    {
		baseDesignator = bd;
		index = i;
	    }

	    public SymbolTable.TypeDesignator type (SymbolTable table)
	    {
		SymbolTable.TypeDesignator type = baseDesignator.type (table);
		if (type == null) return null;
		else              return type.dereferencedType ();
	    }

	}

    }

    public class Number implements Expression
    {
	short value;
	Number (short v) { value = v; }
	public SymbolTable.TypeDesignator type (SymbolTable table) { return SymbolTable.TypeDesignator.SHORT; }
    }

    public class ProcedureCall implements Expression
    {

	String name;
	List <Expression> arguments;

	ProcedureCall (String n, List <Expression> a)
	{
	    name = n;
	    arguments = a;
	}

	public SymbolTable.TypeDesignator type (SymbolTable table)
	{
	    SymbolTable.Symbol symbol = table.getBinding (name, "PROC");
	    if (symbol == null) return null;
	    else                return symbol.type ();
	}

    }

    abstract class BinaryOperation implements Expression
    {

	Expression expression0, expression1;

	BinaryOperation (Expression e0, Expression e1)
	{
	    expression0 = e0;
	    expression1 = e1;
	}

	public SymbolTable.TypeDesignator type (SymbolTable table)
	{
	    return SymbolTable.TypeDesignator.Combine.symetrically (expression0.type (table), expression1.type (table));
	}

	public static class Addition       extends BinaryOperation
	{
	    Addition       (Expression e0, Expression e1) { super (e0, e1); }
	}

	public static class Subtraction    extends BinaryOperation
	{
	    Subtraction    (Expression e0, Expression e1) { super (e0, e1); }
	}

	public static class Multiplication extends BinaryOperation
	{
	    Multiplication (Expression e0, Expression e1) { super (e0, e1); }
	}

	public static class Division       extends BinaryOperation
	{
	    Division       (Expression e0, Expression e1) { super (e0, e1); }
	}

    }

}
