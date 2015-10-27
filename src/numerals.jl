## Numerals - Construct numerals
## =============================

# TODO: Add support for all leaf types

## Constructing Sorts
## =================
mk_num(::Type{Bool}) = mk_bool
mk_num(::Type{Real}) = mk_real
mk_num(::Type{Int32}) = mk_int
mk_num(::Type{Int64}) = mk_int64
mk_num(::Type{UInt64}) = mk_unsigned_int64
mk_num(::Type{UInt}) = mk_unsigned_int

mk_sort(::Type{Bool}) = BoolSort
mk_sort(::Type{Real}) = RealSort
mk_sort(::Type{Integer}) = IntSort

## Integer Numerals
## ================
function NumeralAst{T <: IntegerTypes}(::Type{T}, v::Int32; ctx::Context = global_ctx())
  NumeralAst{T}(mk_int(ctx, v, mk_sort(T)(ctx=ctx)))
end

function NumeralAst{T <: IntegerTypes}(::Type{T}, v::Int64; ctx::Context = global_ctx())
  NumeralAst{T}(mk_int64(ctx, v, mk_sort(T)(ctx=ctx)))
end

function NumeralAst{T <: IntegerTypes}(::Type{T}, v::UInt32; ctx::Context = global_ctx())
  NumeralAst{T}(mk_unsigned_int(ctx, v, mk_sort(T)(ctx=ctx)))
end

function NumeralAst{T <: IntegerTypes}(::Type{T}, v::UInt64; ctx::Context = global_ctx())
  NumeralAst{T}(mk_unsigned_int64(ctx, v, mk_sort(T)(ctx=ctx)))
end

## Rational Numerals
## =================

function NumeralAst(::Type{Real}, v::Rational{Int32}; ctx::Context = global_ctx())
  NumeralAst{Real}(mk_real(ctx, Int32(v.den), Int32(v.num)))
end

function NumeralAst(::Type{Real}, v::Rational{Int64}; ctx::Context = global_ctx())
  NumeralAst(Real, "$(v.den)/$(v.num)"; ctx=ctx)
end

"Construct real valued numeral from integer by converting to rational"
function NumeralAst(::Type{Real}, v::Integer; ctx::Context = global_ctx())
  NumeralAst{Real}(mk_real(ctx, Int32(v), Int32(1)))
end

"Construct float numeral from rational conversion of float"
function NumeralAst(::Type{Real}, v::Float64; ctx::Context = global_ctx())
  NumeralAst(Real, Rational(v); ctx=ctx)
end

"Construct real numeral from string"
function NumeralAst{T <: NumberTypes}(::Type{T}, v::ASCIIString; ctx::Context = global_ctx())
  NumeralAst{Real}(mk_numeral(ctx, v, mk_sort(T)(ctx=ctx)))
end

## Bool
function NumeralAst(x::Bool; ctx::Context = global_ctx())
  NumeralAst{Bool}(x ? mk_true(ctx) : mk_false(ctx))
end

# Defaults
NumeralAst(v::Integer; ctx::Context = global_ctx()) = NumeralAst(Integer, v; ctx = ctx)
NumeralAst(v::Real; ctx::Context = global_ctx()) = NumeralAst(Real, v; ctx = ctx)
NumeralAst(v::ASCIIString; ctx::Context = global_ctx()) = NumeralAst(Real, v; ctx = ctx)
