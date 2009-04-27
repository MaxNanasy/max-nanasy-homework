type newType = short;

void sym1(newType a) {
     a = 1;
}

main()
{
  var a : newType;
  a = 1 + ::sym1(a);
}
