----------------------------------------------------------------------------
-- An interpreter that expands refs.
-- Removes the neccessity for
-- ref on the interpreter it is called on.
---------------------------------------------------------------------------
local expand_ref = {}
function expand_ref.e()
   return function (i)
      return i.e()
   end
end

function expand_ref.seq(rule1, rule2)
   return function (i)
      return i.seq(rule1(i), rule2(i))
   end
end

function expand_ref.lit(lit)
   return function (i)
      return i.lit(lit)
   end
end

function expand_ref.choice(rule1, rule2)
   return function (i)
      return i.choice(rule1(i), rule2(i))
   end
end

function expand_ref.ref(rule, rules)
   return rules[rule]
end

function expand_ref.star(item)
   return function (i)
      i.star(item(i))
   end
end

function expand_ref.grammar(item)
   return function (interpreter)
      return interpreter.grammar(item(interpreter))
   end
end

function expand_ref.create(grammar)
   return function (interpreter)
      return interpreter.create(grammar(interpreter))
   end
end

return expand_ref
