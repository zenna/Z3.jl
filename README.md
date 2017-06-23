# Z3.jl

[![Build Status](https://travis-ci.org/zenna/Z3.jl.svg?branch=master)](https://travis-ci.org/zenna/Z3.jl)

This is a Julia interface to Z3 - a high performance theorem prover developed at Microsoft Research.
Z3 can solve [satisfiability modulo theory (SMT)](https://en.wikipedia.org/wiki/Satisfiability_modulo_theories) problems.

## Install

*Prerequisites*: Have Z3 installed with shared libraries in your path.

```julia
Pkg.clone("git@github.com:zenna/Z3.jl.git")
```


## Usage


```julia
using Z3.jl
```

```julia
using Z3
A = Var(Integer)    # Create an integer-valued variable
add!(A - 5 == 10)   # Add a constraint
check()             # Is this problem satisfiable?
model(Int, A)       # Return a value for A in type Int = i.e. 15
```

## API Details

Z3.jl is a relatively lightweight wrapper.
By this I mean there's mostly direct access to the C-API, and Z3.jl doesn't prevent Z3 from terminating your program if you use it incorrectly.
There are some conveniences however.  In particular:

### Global Context
Building expressions (and pretty much everything else) in Z3 all take place within a `context`.
Z3.jl provides a Context class which allows you to create a new Context

```julia
ctx = Context()
ctx = Context(qf_bv)  # context under quantifier free bitvector logic
```

All api functions which need a context (which again is most of them), take a `ctx` keyword parameter, e.g.:

```julia
ctx = Context()
A = Var(Integer; ctx=ctx)
B = Var(Integer; ctx=ctx)
C = (-)(A, B; ctx=ctx)
```

This can get quite cumbersome, and so for the common case where you just want to write down an expression, Z3.jl provides a default, globally defined context.
You can access it with `global_ctx()`.

### Global Solver
Much like a global context, many operations (particularly those involved in adding and removing constraints) involve a `solver`.  In Z3.jl solvers are created using the `Solver` type.

```julia
s = Solver() # Equivalently s = Solver(ctx=global_context())
A = Var(Real)
B = Var(Real)
add!(A == B; solver = s)
check(;solver = s)
```

__Warning__: Ensure you don't mix and match variables and assertions with different contexts and solvers or Z3 will probably crash.  This is particularly easy to do with arithmetic operations and the global context.  One way to ensure you are not usung the global context when you don't mean to is to call disable_global_context!() which will throw an error if you attempt to use it.

### A plethora of types and api calls
Z3 has a large api with lots of function calls and lots of types.  All of these can be found in [wrap.jl](https://github.com/zenna/Z3.jl/blob/master/src/wrap.jl).  For documentation of what parts mean, check the [Z3 C API documentation](http://research.microsoft.com/en-us/um/redmond/projects/z3/code/group__capi.html)

For every c type we have a corresponding julia type.
All of these types subtype `Z3CType`.

For instance in `wrap.jl` we have the definition:

```julia
@wrap function Z3_mk_eq(ctx::Z3_context,l::Z3_ast,r::Z3_ast)
    ccall((:Z3_mk_eq,"libz3"),Z3_ast,(Z3_context,Z3_ast,Z3_ast),ctx,l,r)
end
```

Note that `Z3_ast` is just a typealias alias `Ptr{Void}`.
This is true for all types that begin with `Z3`.
The corresponding julia type is `Ast`

The `@wrap` performs some creative metaprogramming to create a new function `mk_eq` (prefix `Z3_` has been dropped) which will accept the julia types, and treats `context` arguments instead as keyword parameters, e.g:

```julia
# Return the expression l == r
function mk_eq(l::Ast, r::Ast; ctx::Context = global_context())
  ...
  return x::Ast
end
```

Which can be used more conveniently than dealing with the c pointers.

```julia
A = Var(Integer)
B = Var(Integer)
mk_eq(A, B)
```
