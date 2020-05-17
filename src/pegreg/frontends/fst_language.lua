--------------------------------------------------------------------------------
-- Now that we have all of these layers,
-- we can output states and arrows for _unordered_ choice.
-- States and arrows are another language; they are made of these elements:
-- (state N FINAL)
-- (arrow FROM TO INPUT OUTPUT)
-- (create (pair (state N FINAL) ...) (pair (arrow FROM TO INPUT OUTPUT) ...))
-- Where N is the number of the state,
-- FINPUTAL is whether the state is final or not,
-- L is the list of final states,
-- FROM and TO are the state it comes from and goes to,
-- and INPUT and OUTPUT are the input and output characters.
-- These states and arrows will be made into lists of PAIRs
-- ending with NULLs.
--------------------------------------------------------------------------------
local fstl = {}

function fstl.l()
   local l = {}
   l.states = {}
   l.arrows = {}

   function l:state(n, final)
      self.states[#self.states + 1] = function (interpreter)
         interpreter.state(n, final)
      end
      return self
   end

   function l:arrow(from, to, input, output)
      self.arrows[#self.arrows + 1] = function (interpreter)
         interpreter.arrow(from, to, input, output)
      end
      return self
   end

   function l:create(interpreter)
      local states = interpreter.null()
      for _, v in ipairs(self.states) do
         states = interpreter.pair(v(interpreter), states)
      end

      local arrows = interpreter.null()
      for _, v in ipairs(self.arrows) do
         arrows = interpreter.pair(v(interpreter), arrows)
      end

      interpreter.create(states, arrows)
      return self
   end

   return l
end


return fstl
