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
      end

      ins:finish()
   end
   -- Add the error state
   local ins = it:instr(#dfst.states)
   ins:finish()
   return it
end

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
         -- TODO are we keeping output
         -- seperate on arrows or not?
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
