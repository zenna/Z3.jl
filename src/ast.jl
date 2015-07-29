##  AST
## ====
# abstract syntax tree node. That is, the data-structure used in Z3 to represent
# terms, formulas and types.
function Var{T<: MathNumber}(::Type{T};
                          name::ASCIIString = genvar(),
                          ctx::Context = global_context())
  # safe_add!(name, ctx)
  RealVarAst{T}(mk_var(T, ctx, name))
end

## Constructing Sorts
## =================
mk_sort(::Type{Bool}) = mk_bool_sort
mk_sort(::Type{Real}) = mk_real_sort
mk_sort(::Type{Integer}) = mk_int_sort

## Make variables
## ==============
"Create a variable using the given name and type"
function mk_var(ctx::Context, name::ASCIIString, ty::Sort)
  s::Z3Symbol = mk_string_symbol(ctx, name)
  return mk_const(ctx, s, ty)
end

"Create a variable using the given name and type"
function mk_var(ctx::Context, name::Integer, ty::Sort)
  s::Z3Symbol = mk_int_symbol(ctx, Int32(name))
  return mk_const(ctx, s, ty)
end

"Create a variable using the given name"
function mk_var(::Type{Integer}, ctx::Context, name::Union(ASCIIString, Integer))
  ty = mk_int_sort(ctx)
  mk_var(ctx, name, ty)
end

"Create a variable using the given name"
function mk_var(::Type{Real}, ctx::Context, name::Union(ASCIIString, Integer))
  ty = mk_real_sort(ctx)
  mk_var(ctx, name, ty)
end

"Create a variable using the given name"
function mk_var(::Type{Bool}, ctx::Context, name::Union(ASCIIString, Integer))
  ty = mk_bool_sort(ctx)
  mk_var(ctx, name, ty)
end

## Arithmetic
## ==========

# Real op Real -> Bool
# Real op Integer -> Real op ToReal(Integer)
# Integer op Real -> ToReal(Integer) op Real
# Integer op Integer -> Bool
#
# Real/Integer op Constant -> Real op convert(Real, Constant)
# Constant op Real -> convert(Real, Constant) op Real
#

RealAst = Union(RealVarAst{Real}, VarAst{Real}, AppAst{Real}, NumeralAst{Real})
IntegerAst = Union(RealVarAst{Integer}, VarAst{Integer}, AppAst{Integer}, NumeralAst{Integer})
BoolAst = Union(RealVarAst{Bool}, VarAst{Bool}, AppAst{Bool}, NumeralAst{Bool})

LeafInteger = Union(Float64, Int64,  Int128, Int16, Int32, Int64, Int8, Int128,
  Int16, Int32, Int64, Int8, Bool, BigInt)

LeafFloat = Union(Base.MPFR.BigFloat, Float16, Float32, Float64)
LeafReal = Union(LeafFloat, LeafInteger, Rational)

## Conversion Functions
to_real(x::IntegerAst; ctx::Context=global_context()) = AppAst{Real}(mk_int2real(ctx, x))
to_int(x::RealAst; ctx::Context=global_context()) = AppAst{Integer}(mk_real2int(ctx, x))

real_real_bool = @compat Dict(:(>=) => mk_ge, :(>) => mk_gt,
  :(<=) => mk_le, :(<) => mk_lt, :(==) => mk_eq)

## Real × Real -> Bool
for (op,func) in real_real_bool
  @eval ($op)(x::RealAst, y::RealAst; ctx::Context = global_context()) =
    AppAst{Bool}($func(ctx, x, y))

  @eval ($op)(x::RealAst, y::IntegerAst; ctx::Context = global_context()) =
    ($op)(x, to_real(y; ctx=ctx); ctx=ctx)

  @eval ($op)(x::IntegerAst, y::RealAst; ctx::Context = global_context()) =
    ($op)(to_real(x; ctx=ctx), y; ctx=ctx)

  @eval ($op)(x::IntegerAst, y::IntegerAst; ctx::Context = global_context()) =
    ($op)(x, y; ctx=ctx)

  # Concrete Types
  @eval ($op)(x::RealAst, y::LeafReal; ctx::Context = global_context()) =
    AppAst{Bool}($func(ctx, x, NumeralAst(Real, y)))

  @eval ($op)(x::LeafReal, y::RealAst; ctx::Context = global_context()) =
    AppAst{Bool}($func(ctx, NumeralAst(Real, x), y))

  @eval ($op)(x::IntegerAst, y::LeafInteger; ctx::Context = global_context()) =
    AppAst{Bool}($func(ctx, x, NumeralAst(Integer, y)))

  @eval ($op)(x::LeafInteger, y::IntegerAst; ctx::Context = global_context()) =
    AppAst{Bool}($func(ctx, NumeralAst(Integer, x), y))
end

distinct(x::RealAst...; ctx::Context = global_context()) =
  AppAst{Bool}(mk_distinct(ctx, UInt32(length(x)), Any[x...])) #FIXME: Any[X...] is loose, see other FIXME

#TODO: Add variable arg julia side: e.g. +(1,2,3) and sum([1,2,3])
# Vaarg Real × Real -> Real
# Ambiguity fixes
(*){Q<:Union{Z3.NumeralAst{Real}, Z3.RealVarAst{Real}, Z3.AppAst{Real}}}(x::Bool, y::Q) =
  AppAst{Bool}($func(ctx, NumeralAst(Real, x), y))
(*){Q<:Union{Z3.RealVarAst{Integer}, Z3.AppAst{Integer}, Z3.NumeralAst{Integer}}}(x::Bool, y::Q) =
  (*)(x, NumeralAst(Integer, y); ctx=ctx)

vaarg_real_real_real = @compat Dict(:(-) => mk_sub, :(*) => mk_mul, :(+) => mk_add)
for (op, func) in vaarg_real_real_real
  @eval ($op)(x::RealAst, y::RealAst; ctx::Context = global_context()) =
    AppAst{Real}($func(ctx, Uint32(2), Any[x, y])) #Fixme: Loose type any because X and Y may share no parent

  # FIXME: This is a repeat of above, only need to specify it once
  @eval ($op)(x::RealAst, y::IntegerAst; ctx::Context = global_context()) =
    ($op)(x, to_real(y; ctx=ctx); ctx=ctx)

  @eval ($op)(x::IntegerAst, y::RealAst; ctx::Context = global_context()) =
    ($op)(to_real(x; ctx=ctx), y; ctx=ctx)

  @eval ($op)(x::IntegerAst, y::IntegerAst; ctx::Context = global_context()) =
    AppAst{Integer}($func(ctx, Uint32(2), Any[x, y])) #Fixme: Loose type any because X and Y may share no parent

  # Concrete
  @eval ($op)(x::RealAst, y::LeafReal; ctx::Context = global_context()) =
    ($op)(x, NumeralAst(Real, y); ctx=ctx)

  @eval ($op)(x::LeafReal, y::RealAst; ctx::Context = global_context()) =
    ($op)(NumeralAst(Real, x), y; ctx=ctx)

  #FIXME: What if we can't turn value into integer?, e.g. we need to handle
  # X + 2.3 by convering X to a real
  @eval ($op)(x::IntegerAst, y::LeafInteger; ctx::Context = global_context()) =
    ($op)(x, NumeralAst(Integer, y); ctx=ctx)

  @eval ($op)(x::LeafInteger, y::IntegerAst; ctx::Context = global_context()) =
    ($op)(NumeralAst(Integer, x), y; ctx=ctx)
end

# Ambiguitiy
(^)(x::Union{Z3.RealVarAst{Real}, Z3.NumeralAst{Real}, Z3.AppAst{Real}}, y::Base.Rational) =
  (^)(x, NumeralAst(Real, y); ctx=ctx)


real_real_real = @compat Dict(:(^) => mk_power, :(/) => mk_div, :(+) => mk_add)
for (op, func) in real_real_real
  @eval ($op)(x::RealAst, y::RealAst; ctx::Context = global_context()) =
    AppAst{Real}($func(ctx, x, y))

  # FIXME: This is a repeat of above, only need to specify it once
  @eval ($op)(x::RealAst, y::IntegerAst; ctx::Context = global_context()) =
    ($op)(x, to_real(y; ctx=ctx); ctx=ctx)

  @eval ($op)(x::IntegerAst, y::RealAst; ctx::Context = global_context()) =
    ($op)(to_real(x; ctx=ctx), y; ctx=ctx)

  @eval ($op)(x::IntegerAst, y::IntegerAst; ctx::Context = global_context()) =
    AppAst{Integer}($func(ctx, x, y))

  # Concrete
  # FIXME: DRY
  @eval ($op)(x::RealAst, y::LeafReal; ctx::Context = global_context()) =
    ($op)(x, NumeralAst(Real, y); ctx=ctx)

  @eval ($op)(x::LeafReal, y::RealAst; ctx::Context = global_context()) =
    ($op)(NumeralAst(Real, x), y; ctx=ctx)

  #FIXME: What if we can't turn value into integer?, e.g. we need to handle
  # X + 2.3 by convering X to a real
  @eval ($op)(x::IntegerAst, y::LeafInteger; ctx::Context = global_context()) =
    ($op)(x, NumeralAst(Integer, y); ctx=ctx)

  @eval ($op)(x::LeafInteger, y::RealAst; ctx::Context = global_context()) =
    ($op)(NumeralAst(Integer, x), y; ctx=ctx)
end

# Unary Operators
(-)(x::RealAst; ctx::Context=global_context()) = AppAst{Real}(mk_unary_minus(ctx, x))
(-)(x::IntegerAst; ctx::Context=global_context()) = AppAst{Integer}(mk_unary_minus(ctx, x))

integer_integer_integer = @compat Dict(:(%) => mk_mod, :rem => mk_rem)
for (op, func) in integer_integer_integer
  @eval ($op)(x::IntegerAst, y::IntegerAst; ctx::Context = global_context()) =
    AppAst{Integer}($func(ctx, x, y))

  #FIXME: What if we can't turn value into integer?, e.g. we need to handle
  # X + 2.3 by convering X to a real
  @eval ($op)(x::IntegerAst, y::LeafReal; ctx::Context = global_context()) =
    ($op)(x, NumeralAst(Integer, y); ctx=ctx)

  @eval ($op)(x::LeafInteger, y::RealAst; ctx::Context = global_context()) =
    ($op)(NumeralAst(Integer, x), y; ctx=ctx)
end


bool_bool_bool = @compat Dict(:($) => mk_xor,
  :implies => mk_implies, :mk_iff => :biimplies)
for (op, func) in bool_bool_bool
  @eval ($op)(x::BoolAst, y::BoolAst; ctx::Context = global_context()) =
    AppAst{Bool}($func(ctx, x, y))

  @eval ($op)(x::IntegerAst, y::LeafReal; ctx::Context = global_context()) =
    ($op)(x, NumeralAst(Bool, y); ctx=ctx)

  @eval ($op)(x::LeafInteger, y::RealAst; ctx::Context = global_context()) =
    ($op)(NumeralAst(Bool, x), y; ctx=ctx)
end

vararg_bool_bool_bool = @compat Dict(:(&) => mk_and, :(|) => mk_or)
for (op, func) in vararg_bool_bool_bool
  @eval ($op)(x::BoolAst, y::BoolAst; ctx::Context = global_context()) =
    AppAst{Bool}($func(ctx, Uint32(2), Any[x, y])) #Fixme: Loose type any because X and Y may share no parent

  @eval ($op)(x::IntegerAst, y::LeafReal; ctx::Context = global_context()) =
    ($op)(x, NumeralAst(Bool, y); ctx=ctx)

  @eval ($op)(x::LeafInteger, y::RealAst; ctx::Context = global_context()) =
    ($op)(NumeralAst(Bool, x), y; ctx=ctx)
end

bool_bool =  @compat Dict(:(!) => mk_not)
for (op, func) in bool_bool_bool
  @eval ($op)(x::BoolAst, y::BoolAst; ctx::Context = global_context()) =
    AppAst{Bool}($func(ctx, x, y))
end

ifelse(a::BoolAst, b::BoolAst, c::BoolAst; ctx::Context = global_context()) =
  AppAst{Bool}(mk_ite(ctx, a, b, c))

ifelse(a::BoolAst, b::RealAst, c::RealAst; ctx::Context = global_context()) =
  AppAst{Real}(mk_ite(ctx, a, b, c))

ifelse(a::BoolAst, b::IntegerAst, c::RealAst; ctx::Context = global_context()) =
  AppAst{Real}(mk_ite(ctx, a, to_real(b), c))

ifelse(a::BoolAst, b::RealAst, c::IntegerAst; ctx::Context = global_context()) =
  AppAst{Real}(mk_ite(ctx, a, b, to_real(c)))

ifelse(a::BoolAst, b::IntegerAst, c::IntegerAst; ctx::Context = global_context()) =
  AppAst{Integer}(mk_ite(ctx, a, b, c))

"Is this real number an integer"
is_int(a::RealAst; ctx::Context = global_context()) =
  AppAst{Bool}(is_int(ctx, a,))

# TODO
# Operations on numealasts e.g. Numral(2) + Numeral(2)?
# !=
# find iff symbol
# unary plus (handle ctx properly)
