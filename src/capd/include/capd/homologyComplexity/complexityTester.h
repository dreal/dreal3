/// @addtogroup 2
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file complexityTester.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Marian Mrozek 2005-2006
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 


template<typename ObjectGenerator, typename ResultType>
class ComplexityTester{
  public:
    typedef typename ObjectGenerator::ObjectType ObjectType;
    typedef CRef<ResultType> (*AlgorithmType)(CRef<ObjectType> objectType);
    std::string findComplexity(int A_firstScale,int A_lastScale,int A_step,std::ostream& out);
    ComplexityTester(
      const ObjectGenerator& A_objectGenerator,
      AlgorithmType A_algorithm,
      std::string A_TestType
    ):
      m_objectGenerator(A_objectGenerator),
      m_algorithm(A_algorithm),
      m_testType(A_TestType)
    {}

  private:
     const ObjectGenerator& m_objectGenerator;
     AlgorithmType m_algorithm;
     std::string m_testType;
};
/// @}

