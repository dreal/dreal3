let transform (hm : Hybrid.t) : Dr.t =
  let out = BatIO.stdout in
  begin
    Hybrid.print out hm;
    ([("x", 0.0, 3.5)], Dr.True)
  end
