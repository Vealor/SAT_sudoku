var A binary;
var B binary;
var C binary;
var D binary;
var E binary;

subject to constr1: 2 * A - B - C <= 0;
subject to constr2: 2 * A - B - C >= -1;
subject to constr3: D + E >= 1;

write gtest1;
