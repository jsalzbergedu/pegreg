--------------------------------------------------------------------------------
-- Transform all sequences of the form
-- seq(choice(A, B), K)
-- to the form
-- choice(seq(A, K), seq(B, K))
--------------------------------------------------------------------------------
local sc_to_cs = {}

function sc_to_cs.e()
   return function(f, t, data, interpreter)
      return f(false, interpreter.e(), nil, nil)
   end
end

function sc_to_cs.lit(lit)
   return function(interpreter, f, a, b)
      return f(false, interpreter.lit(lit), nil, nil)
   end
end

local function extract(t, data, a, b)
   return t, data, a, b
end

function sc_to_cs.choice(rule1, rule2)
   return function (interpreter, f, a, b)
      local _, erule1, _, _ = rule1(interpreter, extract, nil, nil)
      local _, erule2, _, _ = rule2(interpreter, extract, nil, nil)
      return f(true, interpreter.choice(erule1, erule2), erule1, erule2)
   end
end

function sc_to_cs.star(item)
   return function (interpreter, f, a, b)
      local _, item, _, _ = item(interpreter, extract)
      return f(false, interpreter.star(item), nil, nil)
   end
end

function sc_to_cs.ref(rule, rules)
   return function (interpreter, f, a, b)
      local t, _, a, b = (rules[rule])(interpreter, extract, nil, nil)
      return f(t, interpreter.ref(rule, rules), a, b)
   end
end

function sc_to_cs.seq(rule1, rule2)
   return function (interpreter, f, a, b)
      local t, left, a, b = rule1(interpreter, extract, nil, nil)
      local _, k, _, _ = rule2(interpreter, extract, nil, nil)
      if t then
         local newleft = interpreter.seq(a, k)
         local newright = interpreter.seq(b, k)
         local newout = interpreter.choice(newleft, newright)
         return f(false, newout, nil, nil)
      end
      return f(false, interpreter.seq(left, k), nil, nil)
   end
end

function sc_to_cs.grammar(item)
   return function (interpreter)
      local _, item, _, _ = item(interpreter, extract, nil, nil)
      return interpreter.grammar(item)
   end
end

function sc_to_cs.create(grammar)
   return function (interpreter)
      return interpreter.create(grammar(interpreter))
   end
end

return sc_to_cs
