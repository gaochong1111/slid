#include <iostream>
#include <vector>
#include <set>
#include <map>

using namespace std;

void f(vector<int>& v)
{
	vector<int> v3(v);
	for (auto i:v3)
		cout << i << endl;
}
class test {
public:
	int a;
};

map<int, test> g()
{
	map<int, test> a;
	test b;
	for (size_t i = 0; i < 5; ++i) {
		b.a = i;
		a[i] = b;
	}
	return a;
}

/*
 *void h(int i=3, int j)
 *{
 *        cout << i << endl;
 *        cout << j << endl;
 *}
 */

int main()
{

	return 0;
}
