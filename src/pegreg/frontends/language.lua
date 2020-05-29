--------------------------------------------------------------------------------
-- A set of methods for creating languages.
--------------------------------------------------------------------------------
local l = {}

--------------------------------------------------------------------------------
-- A set of methods for creating languages.
--------------------------------------------------------------------------------
function l.l()
   local l = {}

   l.rules = {}

   function l:rule(name)
      local rule = {}
      function rule:is(tobind)
         l.rules[name] = tobind
         return l
      end
      return rule
   end

   ----------------------------------------------------------------------------
   -- Create a grammar
   ----------------------------------------------------------------------------
   function l:grammar(item)
      self.grammar = function(interpreter)
         return interpreter.grammar(item(interpreter))
      end
      return l
   end

   ----------------------------------------------------------------------------
   -- Create language out out grammar and rules
   ----------------------------------------------------------------------------
   function l:create(interpreter)
      return interpreter.create(l.grammar(interpreter))
   end

   ----------------------------------------------------------------------------
   -- Literal
   ----------------------------------------------------------------------------
   function l:lit(str)
      return function (interpreter)
         return interpreter.lit(str)
      end
   end

   ----------------------------------------------------------------------------
   -- Sequence
   ----------------------------------------------------------------------------
   function l:seq(rule1, rule2)
      return function (interpreter)
         return interpreter.seq(rule1(interpreter), rule2(interpreter))
      end
   end

   ----------------------------------------------------------------------------
   -- A set of methods for creating languages.
   ----------------------------------------------------------------------------
   function l:choice(rule1, rule2)
      return function (interpreter)
         return interpreter.choice(rule1(interpreter), rule2(interpreter))
      end
   end

   ----------------------------------------------------------------------------
   -- A set of methods for creating languages.
   ----------------------------------------------------------------------------
   function l:ref(rule)
      return function (interpreter)
         return interpreter.ref(rule, self.rules)
      end
   end

   ----------------------------------------------------------------------------
   -- Empty transition
   ----------------------------------------------------------------------------
   function l:e()
      return function (interpreter)
         return interpreter.e()
      end
   end

   return l
end


return l
