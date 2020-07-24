----------------------------------------------------------------------------
-- Expand strings into sequences
---------------------------------------------------------------------------
local expand_string = {}

function expand_string.e()
   return function (interpreter)
      return interpreter.e()
   end
end

function expand_string.seq(rule1, rule2)
   return function (interpreter)
      return interpreter.seq(rule1(interpreter),
                             rule2(interpreter))
   end
end

local function expand_string_rec(interpreter, str, c, acc)
   if str == "" then
      return interpreter.seq(interpreter.lit(c), acc)
   end
   return expand_string_rec(interpreter,
                            str:sub(1, #str - 1),
                            str:sub(#str, #str),
                            interpreter.seq(interpreter.lit(c), acc))
end

function expand_string.lit(lit)
   return function (interpreter)
      assert(type(lit) == "string")
      if lit == "" then
         return interpreter.e()
      end
      local acc = interpreter.e()
      return expand_string_rec(interpreter,
                               lit:sub(1, #lit - 1),
                               lit:sub(#lit, #lit),
                               acc)
   end
end

function expand_string.choice(rule1, rule2)
   return function(interpreter)
      return interpreter.choice(rule1(interpreter), rule2(interpreter))
   end
end

function expand_string.grammar(item)
   return function(interpreter)
      return interpreter.grammar(item(interpreter))
   end
end

function expand_string.ref(rule, rules)
   return function(interpreter)
      return interpreter.ref(rule, rules)
   end
end

function expand_string.create(grammar)
   return function(interpreter)
      return interpreter.create(grammar(interpreter))
   end
end

function expand_string.star(item)
   return function(interpreter)
      return interpreter.star(item(interpreter))
   end
end

return expand_string
