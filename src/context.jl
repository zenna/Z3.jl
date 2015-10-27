
## Global Context - default context for conveniece
#3 ==============

Context(l::Logic) = mk_context(l)
Context() = mk_context()

create_global_ctx() =
  (global default_global_ctx; default_global_ctx = Context())

function global_ctx()
  # error("global_ctx_disabled")
  (global default_global_ctx; default_global_ctx)
end

function set_global_ctx(ctx::Context)
  global default_global_ctx
  default_global_ctx = ctx
end

function reset_global_ctx()
  delete_ctx!(global_ctx())
  create_global_ctx!(l)
end
