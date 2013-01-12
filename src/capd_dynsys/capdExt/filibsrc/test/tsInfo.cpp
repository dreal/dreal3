bool isPointExpected[] = {

true,

true,

true,

false,

false,

false,

false,

false,

#if defined(FILIB_EXTENDED)
false,

false,

false,

false,

false,

false,

false,

false,

false,

false,

false,

true,

true,

#endif
};



bool isEmptyExpected[] = {

false,

false,

false,

false,

false,

false,

false,

false,

#if defined(FILIB_EXTENDED)
true,

false,

false,

false,

false,

false,

false,

false,

false,

false,

false,

false,

false,

#endif
};



bool isInfiniteExpected[] = {

false,

false,

false,

false,

false,

false,

false,

false,

#if defined(FILIB_EXTENDED)
false,

true,

true,

true,

true,

true,

true,

true,

true,

true,

false,

false,

false,

#endif
};



size_t hasUlpAccTestSetSize[2] = {10, 14};
unsigned int hasUlpAccTestSet1[][2][4] = {

{
  { 0x0, 0x403, 0x2547a, 0xe147ae14 },
  { 0x0, 0x403, 0x2547a, 0xe147ae14 }
},

{
  { 0x1, 0x3ff, 0x19999, 0x9999999a },
  { 0x1, 0x3ff, 0x19999, 0x9999999a }
},

{
  { 0x0, 0x3ff, 0x19999, 0x9999999a },
  { 0x0, 0x3ff, 0x19999, 0x9999999b }
},

{
  { 0x0, 0x3ff, 0x19999, 0x9999999a },
  { 0x0, 0x3ff, 0x19999, 0x9999999b }
},

{
  { 0x1, 0x3ff, 0x3c083, 0x126e978d },
  { 0x1, 0x3ff, 0x3c083, 0x126e978b }
},

{
  { 0x1, 0x3ff, 0x3c083, 0x126e978d },
  { 0x1, 0x3ff, 0x3c083, 0x126e978b }
},

{
  { 0x1, 0x3ff, 0x3c083, 0x126e978d },
  { 0x1, 0x3ff, 0x3c083, 0x126e978b }
},

{
  { 0x0, 0x000, 0x00000, 0x00000000 },
  { 0x0, 0x000, 0x00000, 0x00000003 }
},

{
  { 0x0, 0x400, 0x00000, 0x00000000 },
  { 0x0, 0x400, 0x00000, 0x000003e7 }
},

{
  { 0x0, 0x400, 0x00000, 0x00000000 },
  { 0x0, 0x400, 0x00000, 0x000003e7 }
},

#if defined(FILIB_EXTENDED)
{
  { 0x0, 0x7ff, 0x80000, 0x00000000 },
  { 0x0, 0x7ff, 0x80000, 0x00000000 }
},

{
  { 0x1, 0x7ff, 0x00000, 0x00000000 },
  { 0x0, 0x7ff, 0x00000, 0x00000000 }
},

{
  { 0x0, 0x7fe, 0xfffff, 0xffffffff },
  { 0x0, 0x7ff, 0x00000, 0x00000000 }
},

{
  { 0x1, 0x7ff, 0x00000, 0x00000000 },
  { 0x1, 0x7fe, 0xfffff, 0xffffffff }
},

#endif
};


unsigned int hasUlpAccTestSet2[] = {

0,

100,

0,

1,

1,

2,

10,

3,

100,

1000,

#if defined(FILIB_EXTENDED)
0,

1,

2,

3,

#endif
};


bool hasUlpAccExpected[] = {

true,

true,

false,

true,

false,

true,

true,

true,

false,

true,

#if defined(FILIB_EXTENDED)
false,

false,

false,

false,

#endif
};



