local l = require("pegreg.frontends.language")

--------------------------------------------------------------------------------
-- Add left and right to seq and choice
--------------------------------------------------------------------------------
local add_left_right = {}

function add_left_right.e()
   return function (i)
      return i.e()
   end
end

function add_left_right.lit(lit)
   return function (i)
      return i.lit(lit)
   end
end

function add_left_right.seq(rule1, rule2)
   return function (i)
      return i.seq(i.left(rule1(i)), i.right(rule2(i)))
   end
end

function add_left_right.choice(rule1, rule2)
   return function (i)
     return i.choice(i.left(rule1(i)), i.right(rule2(i)))
   end
end

function add_left_right.grammar(item)
   return function (i)
      return i.grammar(item(i))
   end
end

function add_left_right.ref(rule, rules)
   return rules[rule]
end

function add_left_right.create(grammar)
   return function (i)
      return i.create(grammar(i))
   end
end

function add_left_right.star(item)
   return function (i)
      return i.star(item(i))
   end
end


return add_left_right
