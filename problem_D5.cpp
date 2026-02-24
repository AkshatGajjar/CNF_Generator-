#include <iostream>
#include <vector>
#include <fstream>
#include <string>

using namespace std;

class DaddaCNFGenerator {
private:
    int varCounter;
    vector<vector<int>> clauses;
    vector<vector<int>> partialProducts;
    vector<vector<int>> columns;
    vector<int> result;

    int newVar() {
        return ++varCounter;
    }

    void addANDGate(int out, int in1, int in2) {
        clauses.push_back({-out, in1});
        clauses.push_back({-out, in2});
        clauses.push_back({out, -in1, -in2});
    }

    pair<int,int> addFullAdder(int a, int b, int c) {
        int sum = newVar();
        int carry = newVar();
        
        clauses.push_back({sum, -a, -b, -c});
        clauses.push_back({sum, a, b, -c});
        clauses.push_back({sum, a, -b, c});
        clauses.push_back({sum, -a, b, c});
        clauses.push_back({-sum, a, b, c});
        clauses.push_back({-sum, -a, -b, c});
        clauses.push_back({-sum, -a, b, -c});
        clauses.push_back({-sum, a, -b, -c});
        
        clauses.push_back({-carry, a, b});
        clauses.push_back({-carry, a, c});
        clauses.push_back({-carry, b, c});
        clauses.push_back({carry, -a, -b});
        clauses.push_back({carry, -a, -c});
        clauses.push_back({carry, -b, -c});

        return {sum, carry};
    }

    pair<int, int> addHalfAdder(int a, int b) {
        int sum = newVar();
        int carry = newVar();
        
        clauses.push_back({-sum, -a, b});
        clauses.push_back({-sum, a, -b});
        clauses.push_back({sum, a, b});
        clauses.push_back({sum, -a, -b});
        
        clauses.push_back({-carry, a});
        clauses.push_back({-carry, b});
        clauses.push_back({carry, -a, -b});
        
        return {sum, carry};
    }

    void generatePartialProducts(const vector<int>& a, const vector<int>& b) {
        partialProducts.assign(9, vector<int>(9, 0));
        for(int i = 0; i < 9; i++) {
            for(int j = 0; j < 9; j++) {
                int pp = newVar();
                addANDGate(pp, a[i], b[j]);
                partialProducts[i][j] = pp;
            }
        }
    }

    void arrangeColumns() {
        columns.assign(17, vector<int>());
        for(int i = 0; i < 9; i++) {
            for(int j = 0; j < 9; j++) {
                columns[i + j].push_back(partialProducts[i][j]);
            }
        }
    }

    void daddaReduction() {
        vector<int> daddaSteps = {6, 4, 3, 2};
        
        for(int maxHeight : daddaSteps) {
            for(size_t col = 0; col < columns.size(); col++) {
                while(columns[col].size() > maxHeight) {
                    int temp = columns[col].size() - maxHeight;
                    
                    if(columns[col].size() >= 3 && temp >= 1) {
                        int a = columns[col].back(); columns[col].pop_back();
                        int b = columns[col].back(); columns[col].pop_back();
                        int c = columns[col].back(); columns[col].pop_back();

                        pair<int, int> p = addFullAdder(a, b, c);
                        columns[col].push_back(p.first);
                        if(col + 1 < columns.size()) {
                            columns[col + 1].push_back(p.second);
                        }
                    } else {
                        int a = columns[col].back(); columns[col].pop_back();
                        int b = columns[col].back(); columns[col].pop_back();

                        pair<int, int> p = addHalfAdder(a, b);
                        columns[col].push_back(p.first);
                        if(col + 1 < columns.size()) {
                            columns[col + 1].push_back(p.second);
                        }
                    }
                }
            }
        }
    }

    void finalAddition() { 
        result.assign(18, 0);
        for(size_t i = 0; i < columns.size(); i++) {
            if(columns[i].size() == 3) {
                pair<int,int> p = addFullAdder(columns[i][0], columns[i][1], columns[i][2]);
                result[i] = p.first;
                if(i + 1 > 16) result[i+1] = p.second;
                else columns[i+1].push_back(p.second);  
            }
            else if(columns[i].size() == 2) {
                pair<int,int> p = addHalfAdder(columns[i][0], columns[i][1]);
                result[i] = p.first;
                if(i + 1 > 16) result[i+1] = p.second;
                else columns[i+1].push_back(p.second);  
            } else if(columns[i].size() == 1) {
                result[i] = columns[i][0];
            } else {
                result[i] = newVar();
            }
        }
    }

public:
    DaddaCNFGenerator() : varCounter(1) {
        clauses.reserve(3000); 
    }

    vector<int> generateMultiplicationLogic(const vector<int>& a, const vector<int>& b) {
        generatePartialProducts(a, b);
        arrangeColumns();
        daddaReduction();
        finalAddition();
        return result; 
    }

    void addEquivalenceCheck(const vector<int>& resultA, const vector<int>& resultB) {
        for(size_t i = 0; i < resultA.size(); i++) {
            clauses.push_back({-resultA[i], -resultB[i]});
            clauses.push_back({resultA[i], resultB[i]});
        }
    }

    void exportToDIMACS(const string& filename) {
        ofstream outFile(filename);
        outFile << "p cnf " << varCounter << " " << clauses.size() << "\n";
        for(const auto& clause : clauses) {
            for(int lit : clause) {
                outFile << lit << " ";
            }
            outFile << "0\n";
        }
        outFile.close();
    }
};

int main() {
    DaddaCNFGenerator generator;
    
    vector<int> a(9), b(9);
    for(int i = 0; i < 9; i++) {
        a[i] = i + 1;  
        b[i] = i + 10; 
    }

    vector<int> resultA = generator.generateMultiplicationLogic(a, b);
    
    vector<int> resultB = generator.generateMultiplicationLogic(a, b);

    generator.addEquivalenceCheck(resultA, resultB);
    
    generator.exportToDIMACS("problem_D5.cnf");
    
    cout << "DIMACS file generated successfully." << endl;
    return 0;
}