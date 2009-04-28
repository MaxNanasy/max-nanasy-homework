package rule;

import parser.*;
import java.io.IOException;

import rule.Rule.Parseable;
import rule.Rule.Parseable.*;

public interface Rule
{
    public interface Parseable extends Rule
    {

	public enum ParseStatus { SUCCESS, FAILURE, ERROR, EMPTY }

	public ParseStatus parse (Parser a) throws IOException;

	public class Named implements Parseable
	{

	    String name;
	    Parseable rule;

	    Named (String name, Parseable rule)
	    {
		this.name = name;
		this.rule = rule;
	    }

	    public ParseStatus parse (Parser p) throws IOException
	    {
		p.printRule (name);
		p.tabCount ++;
		ParseStatus ps = rule.parse (p);
		if (ps != ParseStatus.SUCCESS)
		    p.undoPrintRule ();
		p.tabCount --;
		return ps;
	    }

	    public void associate (Parseable rule)
	    {
		this.rule = rule;
	    }

	}

	public final class Constructor
	{

	    public static final Parseable epsilon = new Epsilon ();
	    public static final Parseable empty   = new Empty ();

	    public static final Parseable.Named named (String name, Parseable rule) { return new Named (name, rule); }
	    public static final Parseable.Named named (String name) { return named (name, empty); }
	    public static final Parseable terminal (int symbol) { return new Terminal (symbol); }

	    public static final Parseable concat (Parseable... rules)
	    {
		Parseable ruleList = epsilon;
		for (int i = rules.length - 1; i >=0; i--)
		    ruleList = new Concatenation (rules [i], ruleList);
		return ruleList;
	    }

	    public static final Parseable conjunct (Parseable... rules)
	    {
		Parseable ruleList = empty;
		for (int i = rules.length - 1; i >=0; i--)
		    ruleList = new Conjunction (rules [i], ruleList);
		return ruleList;
	    }

	    public static final Parseable optional (Parseable rule) { return conjunct (rule, epsilon); }

	    public static final Parseable many (Parseable rule)
	    {
		Conjunction manyRule = new Conjunction (epsilon, null);
		manyRule.rule1 = conjunct (concat (rule, manyRule));
		return manyRule;
	    }
	    public static final Parseable many1 (Parseable rule) { return concat (rule, many (rule)); }

	}

    }

}

class Terminal implements Parseable
{

    int symbol;

    Terminal (int symbol)
    {
	this.symbol = symbol;
    }

    public ParseStatus parse (Parser p) throws IOException
    {
	return p.expect (symbol) ? ParseStatus.SUCCESS : ParseStatus.FAILURE;
    }

}

class Epsilon implements Parseable
{
    Epsilon () { }
    public ParseStatus parse (Parser p)
    {
	return ParseStatus.EMPTY;
    }
}
class Empty implements Parseable
{
    Empty () { }
    public ParseStatus parse (Parser p)
    {
	return ParseStatus.FAILURE;
    }
}

class Concatenation implements Parseable
{

    Parseable rule0, rule1;

    Concatenation (Parseable rule0, Parseable rule1)
    {
	this.rule0 = rule0;
	this.rule1 = rule1;
    }

    public ParseStatus parse (Parser p) throws IOException
    {
	ParseStatus ps0 = rule0.parse (p);
	switch (ps0) {
	case SUCCESS:
	    switch (rule1.parse (p)) {
	    case SUCCESS:
	    case EMPTY: return ParseStatus.SUCCESS;
	    default:    return ParseStatus.ERROR;
	    }
	case EMPTY:
	    ParseStatus ps1 = rule1.parse (p);
	    switch (ps1) {
	    case FAILURE:
	    case ERROR: return ParseStatus.ERROR;
	    default:    return ps1;
	    }
		default:        return ps0;
	}
    }

}

class Conjunction implements Parseable
{

    Parseable rule0, rule1;

    Conjunction (Parseable rule0, Parseable rule1)
    {
	this.rule0 = rule0;
	this.rule1 = rule1;
    }

    public ParseStatus parse (Parser p) throws IOException
    {
	ParseStatus ps0 = rule0.parse (p);
	switch (ps0) {
	case FAILURE:
	case EMPTY:
	    return rule1.parse (p);
	default:
	    return ps0;
	}
    }

}
