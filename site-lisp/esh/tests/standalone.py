class AllowWideCharsGlyphScaler(GlyphScaler):
    def __init__(self, cell_width, avg_width):
        """Construct instance based on target CELL_WIDTH and source AVG_WIDTH."""
        GlyphScaler.__init__(self, cell_width)
        self.avg_width = avg_width

    def scale(self, glyph):
        if glyph.width > 0:
            new_width_in_cells = int(math.ceil(0.75 * glyph.width / self.avg_width))
            # if new_width_in_cells > 1:
            #     print("{} is {} cells wide ({} -> {})".format(...))
            GlyphScaler.set_width(glyph, new_width_in_cells * self.cell_width)
