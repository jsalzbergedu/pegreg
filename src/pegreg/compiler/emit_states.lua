local emit_states = {}
local fst_fast = require("fst_fast")

function emit_states.from_abstract(dfst)
   local it = fst_fast.instruction_tape.open()
   for state in dfst:states() do
      local ins = it:instr(dfst:size())
      if state:number() == 0 then
         ins:initial()
      end
      if state:final() then
         ins:final()
      end
      for arrow in dfst:outgoing(state) do
         local fse = ins:get_outgoing(arrow:input())
         fse:set_outstate(arrow:to():number())
         fse:set_outchar(arrow:input())
      end
      ins:finish()
   end
   -- Add the error state
   local ins = it:instr(dfst:size())
   ins:finish()
   return it
end

return emit_states
