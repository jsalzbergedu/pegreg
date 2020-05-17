require("test.pegreg.interpreters.TestPrintFst")

local pegreg = require("pegreg")
local flatten = pegreg.flatten
local fstl = pegreg.fst_language

TestFlatten = {}

function TestFlatten:testFlattenInterpreter()
   TestPrintFst:assertSLInterpreter(flatten)
end
