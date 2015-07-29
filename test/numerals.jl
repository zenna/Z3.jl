using Z3

Z3.NumeralAst(Int32(1))
Z3.NumeralAst(Int32(-1))
Z3.NumeralAst(Int64(-2))
Z3.NumeralAst(Int64(-4))
Z3.NumeralAst(UInt32(1))
Z3.NumeralAst(UInt64(34))

Z3.NumeralAst(Real, Int32(1))
Z3.NumeralAst(Real, Int32(-1))
Z3.NumeralAst(Real, Int64(-2))
Z3.NumeralAst(Real, Int64(-4))
Z3.NumeralAst(Real, UInt32(1))
Z3.NumeralAst(Real, UInt64(34))

Z3.NumeralAst(10/2)
Z3.NumeralAst(10//2)
Z3.NumeralAst(2π)
Z3.NumeralAst("10/7")

Z3.NumeralAst(true)
Z3.NumeralAst(false)
