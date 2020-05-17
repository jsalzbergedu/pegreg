local luaunit = require("luaunit")
local lfs = require("lfs")

lfs.chdir("./src")
package.loaded["pegreg"] = dofile("pegreg.lua")
lfs.chdir("../")

require("test.pegreg.TestInterpreters")

os.exit(luaunit.LuaUnit.run())
