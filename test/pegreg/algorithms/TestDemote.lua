require("test.pegreg.algorithms.TestNFAToDFA")

local luaunit = require("luaunit")
TestDemote = {}

function TestDemote:abstract_from_arrows(arrows)
   local abstract = TestNFAToDFA:abstract_from_basic(arrows)
   local impl = {}

   function impl:opposite(node, edge)
      if node == edge:from() then
         return edge:to()
      end
      return edge:from()
   end

   function impl:incoming_edges(node)
      local arrow_list = {}
      for arrow in abstract:arrows() do
         if arrow:to() == node then
            table.insert(arrow_list, arrow)
         end
      end
      table.sort(arrow_list, function (a, b)
                               return a:from():number() < b:from():number()
                             end)
      local idx = 1
      local function it()
         if idx > #arrow_list then
            return nil
         end
         local out = arrow_list[idx]
         idx = idx + 1
         return out
      end
      return it
   end

   function impl:contains(node)
      for state in abstract:states() do
         if node == state then
            return true
         end
      end
      return false
   end

   function impl:children(node)
      local children = {}
      for arrow in abstract:arrows() do
         if arrow:from() == node then
            table.insert(children, arrow:to())
         end
      end
      table.sort(children, function (a, b) return a:number() < b:number() end)
      local idx = 1
      local function it()
         if idx < #children then
            return nil
         end
         local out = children[idx]
         idx = idx + 1
         return out
      end
      return it
   end

   function impl:edges()
      return abstract:arrows()
   end

   function impl:verticies()
      return abstract:states()
   end

   local abstract_impl = getmetatable(abstract)
   setmetatable(impl, {__index = abstract_impl})
   return setmetatable(abstract, impl)
end

-- Tests
-- (A/B) K
-- (a/aa)b
function TestDemote:testAOrderedChoiceAAB()
   local q0 = 0
   local a0 = 1
   local af = 2
   local kf = 3
   local b0 = 4
   local b1 = 6
   local bf = 7
   local arrows = {
      {
         {q0, false},
         {a0, false},
         {af, false},
         {kf, true},
         {b0, false},
         {b1, false},
         {bf, false}
      },
      {
         {q0, a0, ''},
         {q0, b0, ''},
         {a0, af, 'a'},
         {b0, b1, 'a'},
         {b1, bf, 'a'},
         {af, kf, 'b'},
         {bf, kf, 'b'}
      }
   }
   local abstract = TestDemote:abstract_from_arrows(arrows)
end

return TestDemote
