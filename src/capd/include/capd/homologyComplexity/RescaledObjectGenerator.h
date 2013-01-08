template<typename InObject, typename OutObject>
class RescaledObjectGenerator{
  public:
    typedef OutObject ObjectType;
    RescaledObjectGenerator(CRef<InObject> A_inObjectCR):m_baseInObjectCR(A_inObjectCR){}
    CRef<ObjectType> getObjectCR(int s){
      InObject baseInObjectCopy( m_baseInObjectCR() );
      baseInObjectCopy.rescale(s);
      return CRef<OutObject>(new OutObject(baseInObjectCopy) )  ;
    }
  private:
    CRef<InObject> m_baseInObjectCR;
};
