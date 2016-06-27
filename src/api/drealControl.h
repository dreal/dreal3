#include<iostream>
#include<vector>
#include<assert.h>
#include "dreal.hh"

namespace dreal {

void checkBarrier(std::vector<expr>& x, std::vector<expr>& f, expr& B, double eps);
void checkLyapunov(std::vector<expr>& x, std::vector<expr>& f, expr& V, double eps);
void synthesizeLyapunov(std::vector<expr*>& x, std::vector<expr*>& p, std::vector<expr*>& f, expr& V, double eps);
void synthesizeControlAndLyapunov(std::vector<expr*>& x, std::vector<expr*>& p_f, std::vector<expr*>& p_v, std::vector<expr*>& f, expr& V, double eps);

}
