local luaunit = require("luaunit")
local lfs = require("lfs")

local requires = {}
local test_requires = {}

local name_to_module = {}

do
   -- Load tests
   lfs.chdir("test")
   for file in lfs.dir(".") do
      if file:sub(1, 4) == "Test" and
         file:sub(-4, -1) == ".lua"
      then
         local suite = dofile(file)
         local name = file:sub(1, -5)
         name_to_module[name] = suite
         _G[name] = suite
         print("Suite is: ")
         requires[name] = suite:requires()
      end
   end

   -- Resolve dependencies
   lfs.chdir("../src")
   for name, requires in pairs(requires) do
      local suite = name_to_module[name]
      suite.luaunit = luaunit
      for _, v in ipairs(requires) do
         if name_to_module[v] == nil then
            name_to_module[v] = require(v)
         end
         suite[v] = name_to_module[v]
      end
   end

   -- Return to main directory
   lfs.chdir("..")

end

os.exit(luaunit.LuaUnit.run())
