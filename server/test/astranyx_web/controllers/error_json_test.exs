defmodule AstranyxWeb.ErrorJSONTest do
  use AstranyxWeb.ConnCase, async: true

  test "renders 404" do
    assert AstranyxWeb.ErrorJSON.render("404.json", %{}) == %{errors: %{detail: "Not Found"}}
  end

  test "renders 500" do
    assert AstranyxWeb.ErrorJSON.render("500.json", %{}) ==
             %{errors: %{detail: "Internal Server Error"}}
  end
end
