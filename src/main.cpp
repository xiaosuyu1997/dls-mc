#include <algorithm>
#include <assert.h>
#include <cmath>
#include <cstdio>
#include <cstring>
#include <fstream>
#include <iostream>
#include <list>
#include <math.h>
#include <set>
#include <stdlib.h>
#include <string.h>
#include <string>
#include <time.h>
#include <ctime>
#include <vector>

using namespace std;

#define FILEINPUT
#define RANDOMCHOOSE
//#define DEBUG

#define MAXN 760
#define INF 999999
#define penaltyDelay 1 // 20
#define MAXP 100

typedef int Vertex;
int N = 0, M = 0;
int maxSteps = 50000;
int numSteps = 0;

void changemaxsteps()
{
	maxSteps = N * 1000;
}

// maintain vertexes information currently in clique
class CliqueSet
{
public:

	int vertexNum;
	Vertex vertexArray[MAXN];
	int indexArray[MAXN];

	CliqueSet()
	{
		clear();
	}

	void insertVertex(Vertex v);
	void deleteVertex(Vertex v);

	vector<Vertex> NL(); // 与C内除一个节点以外不连边，返回节点和在C内和此节点不连边的节点
	vector<Vertex> NI(); // 与C内所有节点都连边

	bool vertexInClique(Vertex v);

	void copy(CliqueSet& o)
	{
		clear();
		vertexNum = o.vertexNum;
		memcpy(vertexArray, o.vertexArray, sizeof(vertexArray));
		memcpy(indexArray, o.indexArray, sizeof(indexArray));
	}

	void clear()
	{
		vertexNum = 0;
		memset(vertexArray, 0, sizeof(vertexArray));
		for (int i = 0; i < MAXN; ++i)
			indexArray[i] = -1;
	}

	inline vector<Vertex> complement()
	{
		vector<Vertex> com;
		for (int i = 1; i <= N; i++)
		{
			if (indexArray[i] == -1)
				com.push_back(i);
		}
		return com;
	}
} C, best_C;

class Graph
{
public:
	int numVertex;
	int numEdge;
	int adjMatrix[MAXN][MAXN];
	// vector<vector<int>> adjList;

	int vertexPenalty[MAXN];
	bool usedInCycle[MAXN];

	int curCycle;

	Graph()
	{
		clear();
	}

	Vertex selectMinPenalty(vector<Vertex> set, bool); // 随机选取具有MinPenalty的Vertex
	void updatePenalty();							   // 根据CliqueSet C

	void restartUsedArray()
	{
		memset(usedInCycle, 0, sizeof(usedInCycle));
	}

	void read_clq(string filename)
	{
		ifstream f(filename.c_str());
		string buffer;
		assert(f.is_open());
		while (!getline(f, buffer).eof())
		{
			if (buffer[0] == 'e')
			{
				int vi, vj;
				sscanf(buffer.c_str(), "%*c %d %d", &vi, &vj);
				adjMatrix[vi][vj] = 1;
				adjMatrix[vj][vi] = 1;
			}
			else if (buffer[0] == 'p')
			{
				char ss[20];
				sscanf(buffer.c_str(), "%*c %s %d", ss, &N);
				numVertex = N;
			}
		}
	}

	bool readGraph()
	{
		clear();
		if (scanf("%d %d", &N, &M) == -1)
			return false;
		changemaxsteps();
		numVertex = N;
		numEdge = M;
		for (int i = 0; i < M; ++i)
		{
			int vi, vj;
			scanf("%d%d", &vi, &vj);
			adjMatrix[vi][vj] = 1;
			adjMatrix[vj][vi] = 1;
		}

		return true;
	}

	void clear()
	{
		numVertex = 0;
		numEdge = 0;
		memset(adjMatrix, 0, sizeof(adjMatrix));
		// adjList.clear();
		memset(vertexPenalty, 0, sizeof(vertexPenalty));
		memset(usedInCycle, 0, sizeof(usedInCycle));
		curCycle = 0;
	}
} G;

void CliqueSet::insertVertex(Vertex v)
{
	if (vertexInClique(v))
		return;
	indexArray[v] = vertexNum;
	vertexArray[vertexNum++] = v;
}

void CliqueSet::deleteVertex(Vertex v)
{
	if (!vertexInClique(v))
	{
		printf("warning: delete vertex not in cliqueset\n");
		return;
	}

	vertexArray[indexArray[v]] = vertexArray[vertexNum - 1];
	indexArray[vertexArray[vertexNum - 1]] = indexArray[v];
	indexArray[v] = -1;
	vertexNum--;
}

bool CliqueSet::vertexInClique(Vertex v)
{
	return indexArray[v] != -1;
}

// 与C内除一个节点以外不连边
vector<Vertex> CliqueSet::NL()
{
	vector<Vertex> nl;
	for (int i = 1; i < G.numVertex; ++i)
	{
		if (vertexInClique(i))
			continue;
		bool onemiss = false;
		bool morethanone = false;
		Vertex missVertex = 0;
		for (int j = 0; j < vertexNum; ++j)
		{
			if (!G.adjMatrix[i][vertexArray[j]])
			{
				if (!onemiss)
				{
					onemiss = true;
					missVertex = vertexArray[j];
				}
				else
					morethanone = true;
			}
		}
		if (onemiss && (morethanone == false))
			nl.push_back(i);
	}
	return nl;
}

// 与C内所有节点都连边
vector<Vertex> CliqueSet::NI()
{
	vector<Vertex> ni;
	for (int i = 1; i <= G.numVertex; ++i)
	{
		if (vertexInClique(i))
			continue;
		bool flag = true;
		for (int j = 0; j < vertexNum; ++j)
		{
			if (!G.adjMatrix[i][vertexArray[j]])
			{
				flag = false;
				break;
			}
		}
		if (flag)
			ni.push_back(i);
	}
	return ni;
}

bool cmp(Vertex a, Vertex b)
{
	return G.vertexPenalty[a] < G.vertexPenalty[b];
}

Vertex Graph::selectMinPenalty(vector<Vertex> s, bool flag) // s 可能是NL，也可能是NC
{
	// 注意不选择超过MAXP的
	sort(s.begin(), s.end(), cmp);
	int minValue = INF;
	vector<int> posPool;
	for (vector<Vertex>::iterator i = s.begin(); i != s.end(); ++i)
	{
		if (G.vertexPenalty[*i] <= minValue)
		{
			if (flag)
			{
				if (usedInCycle[*i])
					continue;
			}
			if (G.vertexPenalty[*i] > MAXP)
				continue;
			minValue = G.vertexPenalty[*i];
			posPool.push_back(*i);
		}
		else
			break;
	}
	if (posPool.empty())
		return -1;
	Vertex chosen = posPool[rand() % (posPool.size())];
	G.usedInCycle[chosen] = 1;
	return chosen;
}

void Graph::updatePenalty()
{
	// 将在当前C中的全部 + 1
	for (int i = 0; i < C.vertexNum; ++i)
		vertexPenalty[C.vertexArray[i]]++;
	if (curCycle++ == penaltyDelay)
	{
		curCycle = 0;
		for (int i = 1; i <= G.numVertex; ++i)
			vertexPenalty[i] = max(vertexPenalty[i] - 1, 0);
	}
}

// 根据当前G和C中的内容进行picking，并且加入C
void randomPick()
{
	/*
	// 还要写一个防锁死，干脆重启的版本
	bool chosen = false;
	while (!chosen)
	{
		Vertex v = rand() % G.numVertex + 1;
		if (!C.vertexInClique(v))
		{
			chosen = true;
			for (int i = 0; i < C.vertexNum; ++i)
			{
				Vertex v2 = C.vertexArray[i];
				if (G.adjMatrix[v][v2] == 0)
					C.deleteVertex(v2);
			}

			C.insertVertex(v);
		}
	}
	*/
	vector<Vertex> com = C.complement();
	Vertex v = com[rand() % com.size()];

	vector<Vertex> toDelete;
	for (int i = 0; i < C.vertexNum; i++)
	{
		Vertex v2 = C.vertexArray[i];
		if (G.adjMatrix[v][v2] == 0)
			toDelete.push_back(v2);
	}
	for (int i = 0; i < toDelete.size(); ++i)  C.deleteVertex(toDelete[i]);
	C.insertVertex(v);
}

// 返回最后加入的边
Vertex expand()
{
	vector<Vertex> ni = C.NI();
	Vertex v;
	while (!ni.empty())
	{
		v = G.selectMinPenalty(ni, 0);
		if (v == -1)
			return v;
		C.insertVertex(v);
		numSteps++;
		ni = C.NI();
	}
	return v;
}

bool intersect(CliqueSet& c1, CliqueSet& c2)
{
	for (int i = 0; i < c1.vertexNum; ++i)
		if (c2.vertexInClique(c1.vertexArray[i]))
			return true;
	return false;
}

// 返回最后加入的边
Vertex plateauSearch()
{
	Vertex v = -1;

	vector<int> ni = C.NI();
	vector<int> nl = C.NL();
	CliqueSet tmpC;
	tmpC.copy(C);
	while (ni.empty() && !nl.empty() && intersect(tmpC, C))
	{
		v = G.selectMinPenalty(nl, 1);
		if (v == -1)
			break;
		// 找到和v不相连的Vertex u并且删去
		Vertex u;
		for (int i = 0; i < C.vertexNum; ++i)
		{
			u = C.vertexArray[i];
			if (G.adjMatrix[v][u] == 0)
				break;
		}
		C.deleteVertex(u);
		// 插入v
		C.insertVertex(v);

		ni = C.NI();
		nl = C.NL();

		numSteps++;
	}
	return v;
}

void DLS_MC()
{
	numSteps = 0;
	C.clear();
	randomPick();
	Vertex v = -1, u = -1;
	while (numSteps < maxSteps)
	{
		vector<Vertex> ni = C.NI();
		while (!ni.empty())
		{
			u = expand();
			if (u == -1)
				break;
			v = plateauSearch();
			ni = C.NI();
		}
		// TODO，这里补充记录
#ifdef DEBUG
		printf("clique: %d; numSteps: %d\n", C.vertexNum, numSteps);
#endif
		if (C.vertexNum > best_C.vertexNum)
			best_C.copy(C);

		G.updatePenalty();
		G.restartUsedArray();

#ifndef RANDOMCHOOSE
		if (penaltyDelay > 1 && v != -1)
		{
			C.clear();
			C.insertVertex(v);
		}
		else
#endif
			randomPick();
	}

	printf("%d\n", best_C.vertexNum);
	for (int i = 0; i < best_C.vertexNum; ++i)
		if (i == 0)
			printf("%d", best_C.vertexArray[i]);
		else
			printf(" %d", best_C.vertexArray[i]);
	printf("\n");
}

int main()
{

#ifdef DEBUG
	srand(10);
#else
	srand(time(NULL));
#endif
#ifdef FILEINPUT
	G.read_clq("57.clq");
	DLS_MC();
#else
	while (G.readGraph())
	{
		best_C.clear();
		DLS_MC();
	}
#endif

	system("pause");
	return 0;
}