type newType = short;

void sym1(newType a) {
     a = 1;
}

main()
{
  type newType = int;
  var a : newType;
  ::sym1(a);
}
