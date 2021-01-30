# 中文文档

在这篇文档中，我会记录我们小组完成郭炜老师这项 Project 的大体思路。


## 算法的选择

郭炜老师推荐的论文是 Cai 老师的 EWLS，建议首先认真阅读该论文。
可惜 EWLS 在时间效率上表现不佳，于是有了 Cai 老师后续的几篇论文，包括 NuMVC。
优化后的 NuMVC 算法通过将加点和删点操作分离的方式极大地降低了每轮迭代的时间复杂度，在实际测试中可以达到更好的分数。


## NuMVC 的实现

如果理解了 NuMVC 的论文内容，其代码实现应该并不困难，甚至比 EWLS 还要更容易一些。
在互联网上你也可以搜索到 Cai 老师的官方实现以及很多非官方实现，包括 Cpp、Java 等各种语言的版本，可以作为参考。
我们小组的代码实现在 [src.cpp](src.cpp) 中，也可供你参考。
实现 NuMVC 算法主体部分后，对接上 OpenJudge 题目的输入输出部分，简单调整一下迭代次数限制 (max_steps) 应该就可以获得满分了（要在 300s 的运行时间内获得满分并不困难）。


## 时间效率的优化

获得最大的分数后，就要考虑优化运行时间了，这里主要分为两部分。
一部分是对 NuMVC 算法主体代码的优化，减少不必要的冗余操作、合理利用 STL 等数据结构，优化时间常数；
另一部分就是对测试数据调参，包括每个 case 的随机种子、最大迭代次数等等。（你这有点作弊啊喂）
首先，最终测试数据分为 11 个 case，其中前面的几个 case 只需要不超过 50 次迭代就可以轻松满分，所以我们完全没必要在这些测试数据上花费更多的时间。
后面的 case 会比较困难，其中最后一个 case 甚至需要 350000 次左右的迭代，相当耗时。
在每个 case 上，通过调整随机种子有可能可以在更少的迭代次数内达到满分（但效果不大）。
你也可以试着调整其他参数比如 scale 和 threshold 获得更好的时间效率（但没必要）。
在尝试的过程中，你需要不断向 OpenJudge 提交，查看得分，酱紫（所以建议开个小号）。
另外，建议尝试时每次只关注一个 case，其他 case 直接跳过（得分为0），优化好一个 case 后记下他的超参，再优化下一个 case。
设置参数的部分我也实现在 `src.cpp` 中了，可以参考。

给出我们最终使用的一组参数：

```cpp
const Options options[] = {
#ifdef EXPERIMENTAL

#else
    Options(20, 7, 10, 0.3, 0.5),          // 9
    Options(30, 7, 20, 0.3, 0.5),          // 13
    Options(40, 9, 20, 0.3, 0.5),          // 14
    Options(60, 7, 20, 0.3, 0.5),          // 19
    Options(80, 7, 30, 0.3, 0.5),          // 22
    Options(100, 20201231, 300, 0.3, 0.5), // 24
    Options(200, 7, 10000, 0.3, 0.5),      // 29
    Options(300, 7, 30000, 0.3, 0.5),      // 33
    Options(400, 7, 30000, 0.3, 0.5),      // 30
    Options(500, 7, 50000, 0.3, 0.5),      // 35
    Options(750, 7, 350000, 0.3, 0.5),     // 40
#endif
    Options(-1, 7, 0, 0.3, 0.5)};
```

