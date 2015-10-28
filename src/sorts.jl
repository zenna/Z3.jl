## Sorts
## =====

## Constructing Sorts from Julia Types
## ===================================
mk_sort(::Type{Bool}) = BoolSort
mk_sort(::Type{Real}) = RealSort
mk_sort(::Type{Integer}) = IntSort

## Constructing Sorts
## =================
UninterpretedSort(s::Z3Symbol;ctx::Context=global_ctx()) =
  UninterpretedSort(mk_uninterpreted_sort(ctx, s))
BoolSort(;ctx::Context=global_ctx()) = BoolSort(mk_bool_sort(ctx))
IntSort(;ctx::Context=global_ctx()) = IntSort(mk_int_sort(ctx))
RealSort(;ctx::Context=global_ctx()) = IntSort(mk_real_sort(ctx))

BitVectorSort(size::Integer; ctx::Context=global_ctx()) = BitVectorSort{size}(mk_bv_sort(ctx, SZ))
# TODO: FiniteDomainSort(;ctx::Context=global_ctx()) = FiniteDomainSort(mk_finiteDomain_sort(ctx))
ArraySort(range::Sort, domain::Sort; ctx::Context=global_ctx()) =
  ArraySort(mk_array_sort(ctx, range, domain))
ArraySort{T1, T2}(range::Type{T1}, domain::Type{T2};ctx::Context=global_ctx()) =
  ArraySort(mk_array_sort(ctx, mk_sort(T1)(ctx=ctx), mk_sort(T2)(ctx=ctx)))

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
