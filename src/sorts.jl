## Sorts
## =====

UninterpretedSort(s::Z3Symbol) = UninterpretedSort(mk_uninterpreted_sort(ctx, s))
BoolSort(;ctx=global_context()) = BoolSort(mk_bool_sort(ctx))
IntSort(;ctx=global_context()) = IntSort(mk_bool_sort(ctx))
RealSort(;ctx=global_context()) = IntSort(mk_real_sort(ctx))

convert{T <: Sort}(::Type{T}, x::UnknownSort) = T(x.ptr)

## Sort Groups
## ===========
typealias NumberSort Union(RealSort, IntSort, BitVectorSort, FiniteDomainSort)
typealias IntegerSort Union(IntSort, BitVectorSort, FiniteDomainSort)
