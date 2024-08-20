module _ = struct
  [%%ocanren_inject
  type nonrec ground = Bad of GT.string GT.list (* OCanren.Std.List.ground *)
  [@@deriving gt ~options:{ gmap }]]
end

module _ = struct
  [%%ocanren_inject
  type nonrec ground = OK of GT.string Std.List.ground (* OCanren.Std.List.ground *)
  [@@deriving gt ~options:{ gmap }]]
end
