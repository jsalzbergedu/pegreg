local emit_states = {}
local fst_fast = require("fst_fast")

function emit_states.from_dfst(dfst)
   local it = fst_fast.instruction_tape.open()

   local state_to_arrow = {}

   for i = 0, #dfst.states - 1, 1 do
      state_to_arrow[i] = {}
   end

   for _, arrow in ipairs(dfst.arrows) do
      table.insert(state_to_arrow[arrow.from], arrow)
   end

   for i, state in ipairs(dfst.states) do
      local ins = it:instr(#dfst.states)
      if i == 1 then
         ins:initial()
      end
      if state.final then
         ins:final()
      end

      for _, arrow in ipairs(state_to_arrow[i - 1]) do
         local fse = ins:get_outgoing(arrow.input)
         fse:set_outstate(arrow.to)
         fse:set_outchar(arrow.output)
         print("Inserted arrow from ", i - 1, "to", arrow.to)
      end

      ins:finish()
   end
   -- Add the error state
   local ins = it:instr(#dfst.states)
   ins:finish()
   return it
end

return emit_states
