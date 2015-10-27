## Sorts
## =====

## Constructing Sorts
## =================
UninterpretedSort(s::Z3Symbol;ctx::Context=global_ctx()) =
  UninterpretedSort(mk_uninterpreted_sort(ctx, s))
BoolSort(;ctx::Context=global_ctx()) = BoolSort(mk_bool_sort(ctx))
IntSort(;ctx::Context=global_ctx()) = IntSort(mk_int_sort(ctx))
RealSort(;ctx::Context=global_ctx()) = IntSort(mk_real_sort(ctx))

convert{T <: Sort}(::Type{T}, x::UnknownSort) = T(x.ptr)

## Sort <-> Julia Type
sorttype(::Union{Type{BoolSort},BoolSort}) = Bool
sorttype(::Union{Type{RealSort},RealSort}) = Real
sorttype(::Union{Type{IntSort},IntSort}) = Integer

## Sort Groups
## ===========
typealias NumberSort Union{RealSort, IntSort, BitVectorSort, FiniteDomainSort}
typealias IntegerSort Union{IntSort, BitVectorSort, FiniteDomainSort}
typealias NumberTypes Union{Integer, Real, BitVector} #FIXME addd finite domain
typealias IntegerTypes Union{Integer, BitVector} #FIXME add finitedomain
