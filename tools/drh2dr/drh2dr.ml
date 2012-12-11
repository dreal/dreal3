let transform (hm : Hybrid.t) : Dr.formula =
  begin
    Hybrid.print BatIO.stdout hm;
    Dr.True
  end
