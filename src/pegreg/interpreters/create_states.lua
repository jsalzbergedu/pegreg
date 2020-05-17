--------------------------------------------------------------------------------
-- An interpreter that takes in enumerated, finally-marked
-- PEGREG syntax and translates it to calls to the
-- state interpreter
--------------------------------------------------------------------------------
local create_states = {}

function create_states.e()
   return function (i, t)
      return i.null()
   end
end

function create_states.lit(lit)
   return function (i, t)
      return i.null()
   end
end

function create_states.seq(rule1, rule2)
   return function (i, t)
      local left = rule1(i, t)
      local right = rule2(i, t)
      return i.pair(left, right)
   end
end

function create_states.choice(rule1, rule2)
   return function (i, t)
      local left = rule1(i, t)
      local right = rule2(i, t)
      return i.pair(left, right)
   end
end

function create_states.star(item)
   return item
end

function create_states.left(item)
   return item
end

function create_states.right(item)
   return item
end

function create_states.fin(item)
   return function (i, t)
      return item(i, true)
   end
end

function create_states.notfin(item)
   return function (i, t)
      return item(i, false)
   end
end

function create_states.mark_n(n, item)
   return function (i, t)
      return i.pair(i.state(n, t), item(i, t))
   end
end

function create_states.grammar(item)
   return function (i)
      return item(i, false)
   end
end

function create_states.ref(rule, rules)
   assert(false, "Refs ought to be expanded")
end

function create_states.create(grammar)
   return function (i)
      return i.create(grammar(i), i.null())
   end
end

return create_states
