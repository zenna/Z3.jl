"""
Create a logical context.
Enable model construction only.
Also enable tracing to stderr and register standard error handler.
"""
function mk_context()
  cfg = mk_config()
  ctx = mk_context(cfg)
  del_config(cfg)
  ctx
end

"Create a context under a specified logic."
function mk_context(l::Logic)
  cfg = mk_config()
  ctx = mk_context(cfg)
  del_config(cfg)
  set_logic(ctx, string(l))
  ctx
end

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
