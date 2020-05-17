local add_left_right = require("pegreg.interpreters.add_left_right")

----------------------------------------------------------------------------
-- An interpreter that marks things as final.
-- It adds the method "fin", (and notfin)
-- its interpreter must implement.
---------------------------------------------------------------------------
local mark_fin = {}

function mark_fin.e()
   return function (t, interpreter)
      if t then
         return interpreter.fin(interpreter.e())
      else
         return interpreter.notfin(interpreter.e())
      end
   end
end

function mark_fin.lit(lit)
   return function (t, interpreter)
      if t then
         return interpreter.fin(interpreter.lit(lit))
      else
         return interpreter.notfin(interpreter.lit(lit))
      end
   end
end

function mark_fin.seq(rule1, rule2)
   return function (t, interpreter)
      return interpreter.notfin(interpreter.seq(rule1(false, interpreter),
                                                rule2(t, interpreter)))
   end
end


function mark_fin.choice(rule1, rule2)
   return function (t, interpreter)
      return interpreter.notfin(interpreter.choice(rule1(t, interpreter), rule2(t, interpreter)))
   end
end

function mark_fin.star(item)
   return function (t, interpreter)
      return interpreter.notfin(interpreter.star(item(t, interpreter)))
   end
end

function mark_fin.left(item)
   return function (t, interpreter)
      return interpreter.notfin(interpreter.left(item(t, interpreter)))
   end
end

function mark_fin.right(item)
   return function (t, interpreter)
      return interpreter.notfin(interpreter.right(item(t, interpreter)))
   end
end

function mark_fin.ref(rule, rules)
   assert(false, "Refs should be expanded")
end

function mark_fin.grammar(item)
   return function (interpreter)
      return interpreter.grammar(item(true, interpreter))
   end
end

function mark_fin.create(grammar)
   return function (interpreter)
      return interpreter.create(grammar(interpreter))
   end
end

return mark_fin
