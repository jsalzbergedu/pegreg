local create_states = require("pegreg.interpreters.create_states")
local create_arrows = require("pegreg.interpreters.create_arrows")

--------------------------------------------------------------------------------
-- States and arrows
--------------------------------------------------------------------------------
local state_arrow = {}

function state_arrow.e()
   return function (f)
      return f(create_states.e(), create_arrows.e())
   end
end

function state_arrow.lit(lit)
   return function(f)
      return f(create_states.lit(lit), create_arrows.lit(lit))
   end
end

local function extract(states, arrows)
   return states, arrows
end

function state_arrow.seq(item1, item2)
   local states_1, arrows_1 = item1(extract)
   local states_2, arrows_2 = item2(extract)
   return function (f)
      return f(create_states.seq(states_1, states_2), create_arrows.seq(arrows_1, arrows_2))
   end
end

function state_arrow.choice(item1, item2)
   local states_1, arrows_1 = item1(extract)
   local states_2, arrows_2 = item2(extract)
   return function (f)
      return f(create_states.choice(states_1, states_2), create_arrows.choice(arrows_1, arrows_2))
   end
end

function state_arrow.grammar(item)
   return item
end

function state_arrow.ref(rule, rules)
   assert(false, "Refs should be expanded")
end

function state_arrow.create(grammar)
   local states, arrows = grammar(extract)
   return function (s)
      local arrows = arrows(s, function (a, b) return a end)(-1)
      return s.create(states, arrows)
   end
end

function state_arrow.left(item)
   local states, arrows = item(extract)
   return function (f)
      return f(create_states.left(states), create_arrows.left(arrows))
   end
end

function state_arrow.right(item)
   local states, arrows = item(extract)
   return function (f)
      return f(create_states.right(states), create_arrows.right(arrows))
   end
end

function state_arrow.fin(item)
   local states, arrows = item(extract)
   return function (f)
      return f(create_states.fin(states), create_arrows.fin(arrows))
   end
end

function state_arrow.notfin(item)
   local states, arrows = item(extract)
   return function (f)
      return f(create_states.notfin(states), create_arrows.notfin(arrows))
   end
end

function state_arrow.mark_n(n, item)
   local states, arrows = item(extract)
   return function (f)
      return f(create_states.mark_n(n, states), create_arrows.mark_n(n, arrows))
   end
end

function state_arrow.star(item)
   assert(false, "TODO")
end

return state_arrow
