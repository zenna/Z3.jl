
## Global Context - default context for conveniece
#3 ==============

Context(l::Logic) = mk_context(l)
Context() = mk_context()

create_global_ctx() =
  (global default_global_context; default_global_context = Context())

function global_context()
  # error("global_context_disabled")
  (global default_global_context; default_global_context)
end

function set_global_ctx(ctx::Context)
  global default_global_context
  default_global_context = ctx
end

function reset_global_ctx()
  delete_ctx!(global_context())
  create_global_ctx!(l)
end
